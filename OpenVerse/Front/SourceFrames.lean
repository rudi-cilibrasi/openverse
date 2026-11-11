/- Thread typed source-frame references through generated refining calls. -/
import OpenVerse.Front.FrameRefs
import OpenVerse.Front.Suspend

namespace OpenVerse.Front.SourceFrames
open OpenVerse

structure Prepared where
  fns : Array Fn
  slots : Array (List VTy)
  sigs : List (List VTy × VTy)
  info : Array FrameRefs.Info
  /-- The referenced ancestor and the hidden parameter holding its frame. -/
  refs : Array (List (String × Nat))
  shared : List (String × String)

/-- Add references after spawn argument types have been inferred and before
    suspension ANF. The extra parameters precede hidden type witnesses. -/
def prepare (tagOf : String → Option Nat) (fns : Array Fn) (slots : Array (List VTy))
    (sigs : List (List VTy × VTy)) (info : Array FrameRefs.Info) : Except String Prepared := do
  let frames : Array (List FrameRefs.Origin) ← fns.mapIdxM fun f fn => do
    let mut acc : List FrameRefs.Origin := []
    for (_, s) in (info[f]?.getD {}).slots do
      if s.frame == fn.name then continue
      if (tagOf s.frame).isNone then
        -- Discovery uses the enclosing suspending context before it knows
        -- whether this lift can wait. An immediate lift has no frame and
        -- its local variables keep ordinary copy-in/copy-out semantics.
        if !fns.any (·.name == s.frame) then throw s!"unknown source frame {s.frame}"
        continue
      if let some old := acc.find? (·.frame == s.frame) then
        if old.args != s.args then throw s!"inconsistent arguments of borrowed frame {s.frame} in {fn.name}"
      else acc := acc ++ [s]
    return acc
  let argBase (f : Nat) := (info[f]?).map (·.explicit) |>.getD fns[f]!.arity
  let ren (f i : Nat) := if i < argBase f then i else i + (frames[f]?.getD []).length
  let refs := frames.mapIdx fun f ss => ss.zipIdx.map fun (s, i) => (s.frame, argBase f + i)
  let mut slots := slots
  let mut sigs := sigs
  let mut info := info
  let mut out := fns
  -- Include every borrowed origin, not only the representative chosen for
  -- a frame parameter. Immediate owners have no escaping storage lifetime.
  let shared := ((info.toList.zip fns.toList).flatMap fun (m, fn) =>
    m.slots.filterMap fun (_, s) =>
      if s.frame == fn.name || (tagOf s.frame).isNone then none else some (s.frame, s.name))
  for f in List.range fns.size do
    let fn := fns[f]!
    let ss := frames[f]!
    let tys ← ss.mapM fun s => do
      let some t := tagOf s.frame | throw s!"borrowed storage has no suspending source frame: {s.frame}"
      return VTy.ref [t] s.args
    let insert (xs : List VTy) := xs.take (argBase f) ++ tys ++ xs.drop (argBase f)
    slots := slots.set! f (insert slots[f]!)
    let (ps, r) := sigs[f]!
    sigs := sigs.set f (insert ps, r)
    let m := info[f]?.getD {}
    if f < info.size then
      info := info.set! f { m with
        slots := m.slots.map fun (i, s) => (ren f i, s),
        copies := m.copies.map fun c => { c with target := ren f c.target, result := ren f c.result } }
    let ref (name : String) : Except String Expr :=
      if name == fn.name then
        if (tagOf name).isSome then pure FrameRefs.current
        else throw s!"an immediate function cannot borrow its own frame: {name}"
      else match (refs[f]!).lookup name with
        | some i => pure (.local i)
        | none => throw s!"{fn.name} has no reference to source frame {name}"
    let rec calls : Expr → Except String Expr
      | .call h es => do
        let es ← es.mapM calls
        let more ← (frames[h]?.getD []).mapM fun s => ref s.frame
        return .call h (es.take (argBase h) ++ more ++ es.drop (argBase h))
      | .assign i e => return .assign i (← calls e)
      | .seq a b => return .seq (← calls a) (← calls b)
      | .prim p es => return .prim p (← es.mapM calls)
      | .heap p es => return .heap p (← es.mapM calls)
      | .ite c t e => return .ite (← calls c) (← calls t) (← calls e)
      | .forE i it f b => return .forE i (← calls it) (← calls f) (← calls b)
      | .loop e => return .loop (← calls e)
      | .ret e => return .ret (← calls e)
      | .print e => return .print (← calls e)
      | e => return e
    out := out.set! f { fn with
      arity := fn.arity + ss.length, nslots := fn.nslots + ss.length,
      body := ← calls (Suspend.renumber (ren f) fn.body) }
  return { fns := out, slots, sigs, info, refs, shared := shared.eraseDups }

/-- Resolve a borrowed variable's final field offset only after every
    function has its final slots and suspension header size. -/
def aliases (p : Prepared) (f : Nat) (baseOf : String → Option Nat) : Except String (List FrameRefs.Slot) := do
  let fn := p.fns[f]!
  let mut acc := []
  for (slot, s) in (p.info[f]?.getD {}).slots do
    if !p.shared.contains (s.frame, s.name) then continue
    let some owner := p.fns.toList.findIdx? (·.name == s.frame)
      | throw s!"unknown source frame {s.frame}"
    let some (origin, _) := (p.info[owner]?.getD {}).slots.find? fun (_, o) =>
        o.frame == s.frame && o.name == s.name
      | throw s!"unknown source variable {s.frame}.{s.name}"
    let some base := baseOf s.frame | throw s!"no fields for source frame {s.frame}"
    let frame ← if s.frame == fn.name then pure FrameRefs.currentSlot
      else match (p.refs[f]?.getD []).lookup s.frame with
        | some i => pure i
        | none => throw s!"missing borrowed frame {s.frame} in {fn.name}"
    acc := acc ++ [{ localSlot := slot, frame, field := base + origin }]
  return acc

/-- Immediate lifted helpers borrow ancestor storage too. Keep their default
    prefix separate so it never initializes the ancestor's live variables. -/
def immediate (S : Sigs) (fn : Fn) (Γ : List VTy) (shared : List FrameRefs.Slot)
    (copies : List FrameRefs.CopyOut) : Except String (Fn × List VTy) := do
  if shared.isEmpty then return (fn, Γ)
  if shared.any (·.frame == FrameRefs.currentSlot) then
    throw s!"an immediate function owns borrowed source storage: {fn.name}"
  let some (ds, b) := Suspend.stripInits (fn.nslots - fn.arity) fn.body
    | throw s!"unexpected initializations in immediate refining helper {fn.name}"
  let rewritten ← FrameRefs.rewrite Γ.toArray shared copies b
  let more ← (rewritten.slots.toList.drop Γ.length).mapM fun t =>
    match Suspend.coreDefault S (Γ.take fn.arity) 0 t with
    | some d => pure d
    | none => throw s!"cannot initialize a source-frame receiver snapshot in {fn.name}"
  return ({ fn with
    nslots := rewritten.slots.size, writes := true,
    body := initPrefixE fn.arity (ds ++ more) rewritten.body }, rewritten.slots.toList)

end OpenVerse.Front.SourceFrames
