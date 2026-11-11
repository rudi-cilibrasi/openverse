/- Preserve the state of an uncaught failure while returning it as data.
   Conditions and filters keep their existing transactional semantics. -/
import OpenVerse.Core.TypeCheck
import OpenVerse.Core.Effects

namespace OpenVerse.Front.FailCapture
open OpenVerse

def marker : Nat := 1000000037

/-- An intermediate body marker. The query conservatively retains the
    generated temporaries' failure effect until lowering. The invalid
    primitive is removed before the Core checks or execution. -/
def marked (typeSlot : Nat) (body failed : Expr) : Expr :=
  .ite (.prim (.tupGet marker) [.local typeSlot, body, failed])
    (.prim .query [.local typeSlot]) (.prim .userErr [])

structure World where
  fns : Array Fn
  slots : Array (List VTy)
  sigs : Sigs
  tries : List (Nat × Nat) := []
  todo : Array (Nat × Nat) := #[]
  /-- The current function; new temporaries are options, except a saved
      dispatch receiver, whose existing default can be reused. -/
  locals : Array VTy := #[]
  defaults : Array Expr := #[]
  rawRet : VTy := .void
  arity : Nat := 0

abbrev M := StateT World (Except String)

def fresh (ty : VTy) (initial : Expr) : M Nat := do
  let i := (← get).locals.size
  modify fun w => { w with locals := w.locals.push ty, defaults := w.defaults.push initial }
  return i

def freshOption (ty : VTy) : M Nat := fresh (.opt ty) (.lit .none)

def infer (e : Expr) (hint : VTy := .void) : M VTy := do
  let w ← get
  if (tc w.sigs w.locals.toList w.rawRet e (some hint)).isSome then return hint
  match tc w.sigs w.locals.toList w.rawRet e none with
  | some t => return t
  | none => throw s!"failure capture cannot type {reprStr e} against {reprStr hint}"

def tryOf (f : Nat) : M Nat := do
  let w ← get
  if let some g := w.tries.lookup f then return g
  let some fn := w.fns[f]? | throw s!"failure capture has no function {f}"
  let some (ps, ret) := w.sigs.fns[f]? | throw s!"failure capture has no signature {f}"
  let g := w.fns.size
  let wrapper : Fn := { name := s!"$outcome{f}_{fn.name}", arity := fn.arity, nslots := fn.nslots, decides := fn.decides, writes := fn.writes, body := .prim .userErr [] }
  modify fun w => { w with
    fns := w.fns.push wrapper, slots := w.slots.push (w.slots[f]!),
    sigs := { w.sigs with fns := w.sigs.fns ++ [(ps, .opt ret)] },
    tries := (f, g) :: w.tries, todo := w.todo.push (f, g) }
  return g

/-- Returns inside an existing transaction still have the original failure
    behavior; only their successful operands acquire the function's new tag. -/
partial def tagReturns : Expr → Expr
  | .ret e => .ret (.prim .mkSome [tagReturns e])
  | .assign i e => .assign i (tagReturns e)
  | .seq a b => .seq (tagReturns a) (tagReturns b)
  | .prim p es => .prim p (es.map tagReturns)
  | .heap p es => .heap p (es.map tagReturns)
  | .call f es => .call f (es.map tagReturns)
  | .ite c t e => .ite (tagReturns c) (tagReturns t) (tagReturns e)
  | .forE i a f b => .forE i (tagReturns a) (tagReturns f) (tagReturns b)
  | .loop b => .loop (tagReturns b)
  | .print e => .print (tagReturns e)
  | e => e

/-- Force a value before continuing. The operation can fail only without
    effects: effectful arguments have already been evaluated, and outcome
    callees return failure as a normal `none` value. -/
def bindValue (e : Expr) (ty : VTy) (k : Expr → M Expr) (failed : Expr) : M Expr := do
  let s ← freshOption ty
  let tail ← k (.prim .query [.local s])
  return .ite (.assign s (.prim .mkSome [e])) tail failed

def bindOutcome (e : Expr) (ty : VTy) (k : Expr → M Expr) (failed : Expr) : M Expr := do
  let s ← freshOption ty
  let tail ← k (.prim .query [.local s])
  return .ite (.assign s e) (.ite (.prim .query [.local s]) tail failed) failed

def callParams (f : Nat) (args : List Expr) (ret : VTy) : M (List VTy) := do
  let w ← get
  let some (ps, out) := w.sigs.fns[f]? | throw s!"failure capture has no signature {f}"
  let bound := (ps.zip args).foldl (fun acc (p, e) =>
    match tc w.sigs w.locals.toList w.rawRet e none with
    | some t => p.bindVars t acc
    | none => acc) []
  let θ := callInst bound out (some ret)
  return ps.map (·.subst θ)

def primHints (op : Prim) (ty : VTy) (es : List Expr) : M (List VTy) := do
  let w ← get
  let common ← match es.findSome? fun e =>
      tc w.sigs w.locals.toList w.rawRet e none with
    | some t => pure t
    | none => pure ty
  return es.zipIdx.map fun (_, i) => match op, ty, i with
    | .mkSome, .opt t, _ => t
    | .mkArr, .arr t, _ => t
    | .mkTup, .tup ts, j => ts[j]?.getD .void
    | .query, t, _ => .opt t
    | .concat, t, _ => t
    | .flatten, t, _ => .arr t
    | .index, t, 0 => .arr t
    | .index, _, _ => .int
    | .arrSet, t, 0 => t
    | .arrSet, _, 1 => .int
    | .arrSet, .arr t, _ => t
    | _, _, _ => common

def heapHints (op : HeapOp) (ty : VTy) (es : List Expr) : M (List VTy) := do
  let w ← get
  match op with
  | .new tag =>
    let fs := w.sigs.classes[tag]?.getD []
    let args := match ty with
      | .ref _ args => args
      | .vref ents args =>
        VTy.viewSlotArgs (w.sigs.pinsOf tag) fs ((ents.find? (·.1 == tag)).map (·.2) |>.getD []) args
      | _ => []
    return fs.map (·.inst args)
  | .set _ => return es.zipIdx.map fun (_, i) => if i == 1 then ty else .void
  | _ => return es.map fun _ => .void

mutual
/-- Change uncaught failure into `failed`, without rolling back its effects.
    Existing conditions and filters are deliberately not transformed. -/
partial def capture (e : Expr) (expected : VTy) (k : Expr → M Expr) (failed : Expr)
    (liftReturn : Bool) : M Expr := do
  let w ← get
  let raw (e : Expr) := if liftReturn then tagReturns e else e
  let ty ← infer e expected
  if !e.mayFail { fns := w.fns.toList, main := 0 } then
    return ← bindValue (raw e) ty k failed
  match e with
  | .lit _ | .local _ | .brk => bindValue (raw e) ty k failed
  | .prim .fail [] => return failed
  | .assign i x =>
    let t := w.locals[i]?.getD .void
    capture x t (fun v => bindValue (.assign i v) t k failed) failed liftReturn
  | .seq a b =>
    capture a .void (fun _ => capture b ty k failed liftReturn) failed liftReturn
  | .ret x =>
    capture x w.rawRet (fun v => pure (.ret (if liftReturn then .prim .mkSome [v] else v))) failed liftReturn
  | .print x =>
    capture x VTy.str (fun v => bindValue (.print v) .void k failed) failed liftReturn
  | .prim p es =>
    let hints ← primHints p ty es
    captureArgs es hints (fun vs => bindValue (.prim p vs) ty k failed) failed liftReturn
  | .heap p es =>
    let hints ← heapHints p ty es
    captureArgs es hints (fun vs => bindValue (.heap p vs) ty k failed) failed liftReturn
  | .call f es =>
    let hints ← callParams f es ty
    captureArgs es hints (fun vs => do
      let g ← tryOf f
      bindOutcome (.call g vs) ty k failed) failed liftReturn
  | .ite c t other =>
    -- Bind the join once so continuations are not copied into both arms.
    let out ← freshOption ty
    let store (v : Expr) : M Expr := pure (.assign out (.prim .mkSome [v]))
    let yes ← match c, t with
      | .heap (.isTag tags) [.local y], .call f (.local y' :: es) => do
        let w ← get
        let inferred := es.mapM fun a => tc w.sigs w.locals.toList w.rawRet a none
        if y == y' then
          if let some hints := inferred then
            -- The checker inferred every argument in the unrefined world.
            -- Save the receiver before arguments can reassign its slot, then
            -- repeat the pure test to retain Typed.dispatch's call shape.
            let recv ← fresh (w.locals[y]!) (w.defaults[y]!)
            let g ← tryOf f
            let args ← captureArgs es hints (fun vs => do
              let call := Expr.ite (.heap (.isTag tags) [.local recv])
                (.call g (.local recv :: vs)) (.prim .userErr [])
              bindOutcome call ty store failed) failed liftReturn
            pure (.seq (.assign recv (.local y)) args)
          else capture t ty store failed liftReturn
        else capture t ty store failed liftReturn
      | _, _ => capture t ty store failed liftReturn
    let no ← capture other ty store failed liftReturn
    let tail ← k (.prim .query [.local out])
    return .seq (.ite (raw c) yes no) tail
  | .forE i it filt body =>
    let elem := w.locals[i]?.getD .void
    let bodyTy := match ty with | .arr t => t | _ => .void
    capture it (.arr elem) (fun src => do
      let body ← capture body bodyTy pure failed liftReturn
      bindValue (.forE i src (raw filt) body) ty k failed) failed liftReturn
  | .loop body =>
    let body ← capture body .void pure failed liftReturn
    bindValue (.loop body) .void k failed

partial def captureArgs (es : List Expr) (hints : List VTy) (k : List Expr → M Expr)
    (failed : Expr) (liftReturn : Bool) : M Expr := do
  match es, hints with
  | [], _ => k []
  | e :: es, t :: ts => capture e t (fun v =>
      captureArgs es ts (fun vs => k (v :: vs)) failed liftReturn) failed liftReturn
  | _ :: _, [] => throw "failure capture has too few argument types"
end

partial def lowerMarkers : Expr → M Expr
  | .ite (.prim (.tupGet tag) [.local hint, body, failed]) _ _ => do
    if tag == marker then
      let body ← lowerMarkers body
      let failed ← lowerMarkers failed
      let some (.opt ty) := (← get).locals[hint]?
        | throw "failure capture marker has no result type"
      capture body ty pure failed false
    else throw "unexpected three-argument tuple projection"
  | .assign i e => return .assign i (← lowerMarkers e)
  | .seq a b => return .seq (← lowerMarkers a) (← lowerMarkers b)
  | .prim p es => return .prim p (← es.mapM lowerMarkers)
  | .heap p es => return .heap p (← es.mapM lowerMarkers)
  | .call f es => return .call f (← es.mapM lowerMarkers)
  | .ite c t e => return .ite (← lowerMarkers c) (← lowerMarkers t) (← lowerMarkers e)
  | .forE i a f b => return .forE i (← lowerMarkers a) (← lowerMarkers f) (← lowerMarkers b)
  | .loop b => return .loop (← lowerMarkers b)
  | .ret e => return .ret (← lowerMarkers e)
  | .print e => return .print (← lowerMarkers e)
  | e => return e

def startFn (f : Nat) : M (Fn × List Expr × Expr) := do
  let w ← get
  let fn := w.fns[f]!
  let Γ := w.slots[f]!
  let ρ := (w.sigs.fns[f]!).2
  let some (initials, body) := stripPrefix w.sigs fn.arity Γ fn.arity (Γ.drop fn.arity) fn.body
    | throw s!"failure capture cannot read defaults of {fn.name}"
  let defaults := (List.range fn.arity).map Expr.local ++ initials
  modify fun w => { w with locals := Γ.toArray, defaults := defaults.toArray, rawRet := ρ, arity := fn.arity }
  return (fn, initials, body)

def finishFn (f : Nat) (fn : Fn) (body : Expr) : M Unit := do
  let w ← get
  let body := initPrefixE fn.arity (w.defaults.toList.drop fn.arity) body
  modify fun w => { w with fns := w.fns.set! f { fn with nslots := w.locals.size, body := body }, slots := w.slots.set! f w.locals.toList }

partial def hasMarker : Expr → Bool
  | .ite (.prim (.tupGet tag) es) t e =>
    tag == marker || es.any hasMarker || hasMarker t || hasMarker e
  | .assign _ e | .ret e | .print e | .loop e => hasMarker e
  | .seq a b => hasMarker a || hasMarker b
  | .prim _ es | .heap _ es | .call _ es => es.any hasMarker
  | .ite c t e => hasMarker c || hasMarker t || hasMarker e
  | .forE _ a f b => hasMarker a || hasMarker f || hasMarker b
  | _ => false

/-- Lower markers and only the outcome callees they need. This leaves
    unmarked programs unchanged, including their function indices. -/
def lower (fns : Array Fn) (slots : Array (List VTy)) (sigs : Sigs) :
    Except String (Array Fn × Array (List VTy) × Sigs) := do
  let run : M Unit := do
    for f in List.range fns.size do
      if hasMarker (← get).fns[f]!.body then
        let (fn, _, body) ← startFn f
        let body ← lowerMarkers body
        finishFn f fn body
    let mut n := 0
    while n < (← get).todo.size do
      let (source, target) := (← get).todo[n]!
      let w ← get
      let fn := w.fns[source]!
      let result ← if fn.body.mayFail { fns := w.fns.toList, main := 0 } then do
          let (_, _, body) ← startFn source
          capture body (← get).rawRet (fun v => pure (.prim .mkSome [v])) (.ret (.lit .none)) true
        else do
          let (ps, ret) := w.sigs.fns[source]!
          modify fun w => { w with
            locals := ps.toArray,
            defaults := ((List.range fn.arity).map Expr.local).toArray, rawRet := ret, arity := fn.arity }
          pure (.prim .mkSome [.call source ((List.range fn.arity).map Expr.local)])
      let wrapper := { (← get).fns[target]! with decides := fn.decides }
      finishFn target wrapper result
      n := n + 1
  let (_, w) ← run.run { fns, slots, sigs }
  return (w.fns, w.slots, w.sigs)

end OpenVerse.Front.FailCapture
