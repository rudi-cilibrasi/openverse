/- Elaboration of a program's field defaults and functions (phases 13–14 of
   `elabProgramCore`); public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Signatures

namespace OpenVerse.Front
open OpenVerse

/-- What each heap effect is, for messages. -/
def fxWhat : String → String
  | "reads" => "reads a var field"
  | "writes" => "sets a var field"
  | "allocates" => "constructs an object that has a var field or is <unique>"
  | k => k

/-- Refuses the first effect `st` has that the effects `allowed` of `name` do
    not, with what has it and what to write. -/
def fxCheck (name : String) (allowed : List String) (st : ESt) : Except String Unit := do
  -- writes first, then reads, then allocations
  let order := ["writes", "reads", "allocates"]
  for k in order do
    for (k', kp, via) in st.fx do
      if k' == k && !allowed.contains k then
        let what := match via with
          | some f => s!"{f}, which has the effect <{k}>"
          | none => fxWhat k
        let spec := if allowed.isEmpty then "<computes>" else String.intercalate "" (allowed.map (s!"<{·}>"))
        let fix := if allowed.isEmpty then "remove <computes>" else s!"add <{k}> or <transacts>"
        throw s!"{kp.show}: {name} {what}, which its effects ({spec}) do not allow: {fix}"

/-- What the elaboration of the fields' defaults gives (`elabFieldDefaults`). -/
structure FieldDefaults where
  /-- What they ask for: methods as values, lazily taken calls' functions and
      subtype dictionaries. -/
  needs : Requests
  /-- Each default's Verse Core code, with its struct's or class's name, its
      field's and its place, for `InitializerConvergence`. -/
  bodies : List (String × String × Pos × Expr)

/-- Construction effects and field defaults, a phase of `elabProgramCore`: a
    class whose objects are mutable or unique allocates, which its declared
    construction effects must allow; and each field default of the structs
    `tops` (classes' included) is elaborated once, with its struct's type
    parameters opaque, and must have only the effects its construction
    allows. -/
def elabFieldDefaults (env : TyEnv) (sigs : Signatures) (tops : List STop) (cdefs : List CDef) :
    Except String FieldDefaults := do
  let allSigs := sigs.all
  -- A mutable or unique instance needs allocation even when no source
  -- expression uses the type. Inherited mutable fields/identity count too.
  for cd in cdefs do
    if let some allowed := env.constructionFx[cd.name]? then
      if env.isUnique cd.name || (env.fields cd.name).any (fun (f, _, _) => env.isVarField cd.name f) then
        fxCheck s!"construction of {cd.name}" allowed
          { fx := [("allocates", cd.pos, none)] }
  let mut fieldNeeds : Requests := {}
  let mut initializerBodies : List (String × String × Pos × Expr) := []
  -- check every field default once, with its struct's type parameters opaque
  -- (a default is elaborated again, at its field's type, at each construction
  -- that omits the field)
  for t in tops do
    match t with
    | .const _ n _ none (.structDef _ _ _ _) =>
      let nps := ((env.sparams.lookup n).getD []).map fun (v, c) => Ty.param v c
      let senv := { env with
        tvars := (env.sparams.lookup n).getD [] |>.map fun (v, c) => (v, Ty.param v c)
        boundFacts := (env.sbounds.lookup n).getD [] }
      let allowed := env.constructionFx[n]?.getD heapFx
      let ctx : Ctx := { sigs := allSigs, sigProg := sigs.prog, types := senv, canFail := true,
                          fnFx := allowed, inDefaultCheck := true }
      for (f, ft, d) in (env.structs.lookup n).getD [] do
        if let some d := d then
          -- (an inherited default sees its home class's type parameters, #39)
          let home := (env.defaultHome.lookup (n, f)).getD n
          let hσ := (((env.sparams.lookup home).getD []).map (·.1)).zip (env.argsAt n nps home)
          let ctx := { ctx with defaults := [(n, f)], types := { senv with tvars := hσ } }
          match (do coerce d.pos (← elabE ctx d (some ft)) ft : EM Expr).run { env } with
          | .ok (body, st) =>
            fxCheck s!"default of field '{f}' of {n}" allowed st
            initializerBodies := initializerBodies ++ [(n, f, d.pos, body)]
            fieldNeeds := fieldNeeds.merge { methods := st.needs.methods, loops := st.needs.loops, subtypes := st.needs.subtypes }
          | .error msg => throw s!"{msg} (in the default of field '{f}' of {n})"
    | _ => pure ()
  return { needs := fieldNeeds, bodies := initializerBodies }

/-- A function or a constant of the program, elaborated (`elabFunctions`):
    its Verse Core code and the types of its slots, where it first calls
    `Err()` (#235), which of its locals live in a source frame (`FrameRefs`),
    what its elaboration asks for, and the lazily taken calls it consumes
    (#246). -/
structure ElaboratedFn where
  fn : Fn
  slotTys : List VTy
  errAt : Option Pos
  frames : FrameRefs.Info := {}
  metadata : MetadataFlow.Info := {}
  needs : Requests
  loopFirst : List LoopUse
  /-- (#515) Its calls in failure contexts (`ESt.failCalls`). -/
  failCalls : Array ((Pos × String) × List Nat)

/-- A function: its body under the type environment `env` (which binds the
    type parameters `tps` of a generic function to themselves), after the
    initialisation of every non-parameter slot (OpenVerse.Core.Typing); its
    frame starts with its parameters, then one hidden parameter per type
    parameter, holding a value of that type. It is elaborated against the
    signatures `allSigs` and the program calls see, `sigProg` (`Signatures`). -/
def elabFn (allSigs : List Sig) (sigProg : Prog) (requests : Requests)
    (env : TyEnv) (p : Pos) (name : String) (ps : List SParam) (ptys : List Ty) (ret : Ty)
    (decides : Bool) (allowed : List String) (tps : List (String × Bool)) (body : SExpr)
    (suspends : Bool := false) (selfTps : List String := [])
    (selfFieldOf : Option (String → Option Nat) := none) (scopeClass : Option String := none)
    (evidenceSignature : Option Sig := none) :
    Except String ElaboratedFn := do
  -- (#209) the values of `selfTps` come from the receiver's hidden
  -- fields, in slots after the hidden parameters: a method's own class's
  -- (`C.M`), or as `selfFieldOf` says (a cast's branch, #250, the cast
  -- target's, of the object, its first parameter too)
  let signature := evidenceSignature.getD {
    idx := 0, name, params := ptys, ret, decides, isConst := false, tparams := tps, selfTps,
    typeValues := ps.zipIdx.filterMap fun (param, i) => if param.typeValue then some i else none }
  let env := signature.typeEnv env
  let frame := signature.frame
  if !frame.valid then throw s!"{p.show}: internal: invalid generic evidence frame for {name}"
  let dictTps := frame.orderedParams
  let selfCls := (name.splitOn ".").headD ""
  let selfField (v : String) : Nat :=
    ((selfFieldOf.getD fun v => env.witnessField? selfCls v) v).getD 0
  -- (a cast's branch, #250: each opened type parameter's value must have
  -- a hidden field to come from, never another field)
  if let some sf := selfFieldOf then
    if let some v := selfTps.find? fun v => (sf v).isNone then
      throw s!"{p.show}: internal error: no hidden field holds a value of the type parameter {v} the cast opens (#250)"
  let env := if selfTps.isEmpty then env else
    { env with dictOrder := dictTps.map (·.1),
               selfWitness := selfTps.map fun v => (v, selfField v) }
  let locals := ((ps.zip (List.range ps.length)).zip ptys).map fun ((prm, i), t) =>
    ({ name := prm.name, slot := i, ty := t, mutable := false, typeValue := prm.typeValue } : Local)
  let locals := locals ++ signature.evidenceLocals
  for (prm, i) in ps.zip (List.range ps.length) do
    if ps.take i |>.any (·.name == prm.name) then throw s!"{p.show}: duplicate parameter '{prm.name}'"
  let base : Ctx := {
    sigs := allSigs
    sigProg := sigProg
    locals := locals.reverse
    types := env
    fnFx := allowed
    canFail := decides
    retTy := ret
    dictBase := frame.witnessBase
    suspends := suspends
    dictVars := dictTps.map (·.1) }
  let ctx ← functionBodyCtx requests base p name tps scopeClass
  let locals := ctx.locals.reverse
  let hidden := frame.hiddenTypes
  let arity := frame.arity
  let st0 : ESt := {
    env, nslots := ps.length + hidden.length, slotTys := (ptys ++ hidden).toArray,
    frameSlots := locals.filterMap fun l => l.storage.map (l.slot, ·) }
  let (receiverInits, st0) ← (elabReceiverEvidence ctx p frame).run st0
  let ((r, _), st) ← elabBody ctx body (some ret) st0
  -- (a result of a type parameter's type as a `comparable`: its box)
  let (e, st) ← (coerceBoxWith elabE ctx p r ret).run st
  -- (a body whose result is the empty value ends with it: `void`, `tuple()`)
  let e := if ret.isUnit then Expr.seq e (.lit .void) else e
  let selfInits : List Expr := (dictTps.drop (dictTps.length - selfTps.length)).map fun (v, _) =>
    .heap (.get (selfField v)) [.local 0]
  let selfInits := selfInits ++ receiverInits
  let inits ← match (st.slotTys.toList.drop (ps.length + hidden.length)).mapM
      (slotDefault env frame.witnessBase frame.argumentTypes []) with
    | .ok ds => pure (selfInits ++ ds)
    | .error msg => throw s!"{p.show}: in {name}: {msg}"
  fxCheck name allowed st
  if name.endsWith ".$block" then
    if let some budget := env.constructionFx[(name.dropEnd ".$block".length).toString]? then
      fxCheck s!"construction block of {(name.dropEnd ".$block".length).toString}" budget st
  let inputs := (locals.filter (·.typeValue)).map (·.slot) ++
    (List.range dictTps.length).map (frame.witnessBase + ·)
  let required := signature.params.zipIdx.filterMap fun (ty, i) =>
    if !signature.typeValues.contains i && (SubtypeEvidence.exposesEvidence env ty ||
        (i == 0 && ((signature.hasReceiver && !name.endsWith ".$block") ||
          ["$Await", "$EvAwait", "$StickyAwait", "$cancelMark"].contains name))) then some i else none
  let metadata : MetadataFlow.Info := {
    pos := p, inputs, required, seeds := inputs ++ st.metadataSeeds, uses := st.metadataUses
    shared := st.frameSlots.map (·.1), metadataWrites := st.metadataWrites
    body := some (initPrefixE arity selfInits e) }
  return { fn := { name, arity, nslots := st.nslots, decides, writes := allowed.contains "writes",
                   body := initPrefixE arity inits e },
           slotTys := spawnParamTypes env name (st.slotTys.toList.map (Ty.toVTy env)), errAt := st.errAt,
           frames := { explicit := ps.length, copies := st.frameCopies, slots := st.frameSlots.map fun (i, s) =>
             (i, { frame := s.frame, name := s.name, args := s.args.map (Ty.toVTy env) }) },
           needs := st.needs, loopFirst := st.loopFirst, failCalls := st.failCalls, metadata }

/-- Function elaboration, a phase of `elabProgramCore`: each function and
    constant of `sigs`, by index (a constant may not hold a mutable object, as
    it is computed at each use), then each generic function, once, with its
    type parameters opaque (`elabFn`). -/
def elabFunctions (env : TyEnv) (sigs : Signatures) (requests : Requests) :
    Except String (Array ElaboratedFn) := do
  let allSigs := sigs.all
  let genvOf (g : Sig) : TyEnv := g.typeEnv env
  -- (the functions, then the generic ones, by index)
  let mut elaborated : Array ElaboratedFn := #[]
  for (top, idx) in sigs.tops.zip (List.range sigs.tops.length) do
    let sig := sigs.sigs[idx]!
    match top with
    | .fn p n ps _ _ _ body =>
      elaborated := elaborated.push (← elabFn allSigs sigs.prog requests env p n ps sig.params sig.ret sig.decides sig.fx [] body sig.suspends
        (evidenceSignature := some sig))
    | .const p n _ _ body =>
      -- a constant is computed at each use, so it would be a new object each
      -- time (until Verse Core has global state)
      if sig.ret.holdsMutable env then
        throw s!"{p.show}: the constant {n} would hold an object with var fields or of a <unique> class, which would be a new one at each use: make it a function"
      let ctx : Ctx := { sigs := allSigs, sigProg := sigs.prog, types := env }
      let (r, st) ← elabBody ctx body (some sig.ret) { env }
      let (e, st) ← (coerce p r.1 sig.ret).run st
      -- slots start like a function's (a class-typed one as a placeholder)
      let inits ← match st.slotTys.toList.mapM (slotDefault env 0 [] []) with
        | .ok ds => pure ds
        | .error msg => throw s!"{p.show}: in {n}: {msg}"
      fxCheck n sig.fx st
      elaborated := elaborated.push {
        fn := { name := n, arity := 0, nslots := st.nslots, decides := false,
                writes := sig.fx.contains "writes", body := initPrefixE 0 inits e }
        slotTys := st.slotTys.toList.map (Ty.toVTy env), errAt := st.errAt, needs := st.needs,
        loopFirst := st.loopFirst, failCalls := st.failCalls
        metadata := {
          pos := p, seeds := st.metadataSeeds, uses := st.metadataUses
          metadataWrites := st.metadataWrites, body := some e } }
    | .classDef .. => pure ()   -- expanded above
  -- each generic function is elaborated once, with its type parameters
  -- opaque, as Verse checks it, into one Verse Core function whose types
  -- mention type variables; `Prog.checkTypes` checks it once, for every
  -- instantiation (`Typed.subst`)
  for (top, g) in sigs.generics.zip sigs.gsigs.toList do
    match top with
    | .fn p n ps _ effs _ body =>
      -- (a class's copy of an interface's default, #53, elaborated in the
      -- interface's scope)
      let scope := copyScope? effs
      elaborated := elaborated.push (← elabFn allSigs sigs.prog requests (genvOf g) p n ps g.params g.ret g.decides g.fx g.tparams body
        g.suspends g.selfTps ((requests.casts.find? (·.name == n)).map fun l => fun v =>
          (l.opened.lookup v).bind (env.witnessField? l.target ·)) scope (some g))
    | _ => pure ()
  return elaborated

end OpenVerse.Front
