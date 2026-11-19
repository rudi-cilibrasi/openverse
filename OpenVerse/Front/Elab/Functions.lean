/- Elaboration of a program's field defaults and functions (phases 13–14 of
   `elabProgramCore`); public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Signatures
import OpenVerse.Front.MetadataReceivers
import OpenVerse.Front.ConstantRange

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
    allows, and not fail (unless `Options.extendedDefaults`). -/
def elabFieldDefaults (env : TyEnv) (sigs : Signatures) (tops : List STop) (cdefs : List CDef)
    (extendedDefaults : Bool := false) :
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
      let ctx : Ctx := { sigs := allSigs, sigProg := sigs.prog, types := senv, canFail := true, bodyFailure := false,
                          fnFx := allowed, inDefaultCheck := true }
      for (f, ft, d) in (env.structs.lookup n).getD [] do
        if let some d := d then
          -- (an inherited default sees its home class's type parameters, #39)
          let home := (env.defaultHome.lookup (n, f)).getD n
          let hσ := (((env.sparams.lookup home).getD []).map (·.1)).zip (env.argsAt n nps home)
          -- (#724) a field's default is a data member's definition: it calls
          -- no function that might not complete (Epic's error 3582), unless
          -- `--extended-defaults` (the compiler's own classes have no
          -- source defaults, but for the module-scoped vars' state)
          let dataMember : Option String :=
            if extendedDefaults then none
            else if n == ModuleVars.stateClass then some s!"the module-scoped var {ModuleVars.shown f}"
            else if n.contains '$' then none
            else some s!"the default of field '{f}' of {n}"
          let ctx := { ctx with defaults := [(n, f)], types := { senv with tvars := hσ }, dataMember }
          match (do coerce d.pos (← elabE ctx d (some ft)) ft : EM Expr).run { env } with
          | .ok (body, st) =>
            if let some msg := divergentCallError st.divergentCalls then throw msg
            -- (a class declares no <decides>, and "Class member initializers
            -- and block clauses are implicitly restricted to have no more
            -- effects than what the class declares", Book of Verse ch. 13;
            -- Effects.versetest:537, 3512)
            if !extendedDefaults && body.mayFail sigs.prog then
              throw s!"{d.pos.show}: the default of field '{f}' of {n} can fail: a field's default is no failure context (Book of Verse ch. 13 and its tests, Effects.versetest)"
            fxCheck s!"default of field '{f}' of {n}" allowed st
            initializerBodies := initializerBodies ++ [(n, f, d.pos, body)]
            fieldNeeds := fieldNeeds.merge
              { methods := st.needs.methods, loops := st.needs.loops, subtypes := st.needs.subtypes, anys := st.needs.anys }
          | .error msg => throw s!"{msg} (in the default of field '{f}' of {n})"
    | _ => pure ()
  return { needs := fieldNeeds, bodies := initializerBodies }

/-- Whether a written type has type values in it: `type`, or a metatype
    the front end writes as an interface, `subtype(c)` and its kin
    (`TypeValues`). -/
partial def STy.mentionsMetatype : STy → Bool
  | .name q => q == "type" || ["subtype(", "castable_subtype(", "concrete_subtype(",
      "castable_concrete_subtype(", "classifiable_subset("].any (q.startsWith ·)
  | .app q ts => STy.mentionsMetatype (.name q) || ts.any STy.mentionsMetatype
  | .arr t | .opt t => t.mentionsMetatype
  | .tup ts => ts.any STy.mentionsMetatype
  | .map k v => k.mentionsMetatype || v.mentionsMetatype
  | _ => false

/-- The defaults of a function's named parameters, each elaborated once at
    the definition, in the function's scope (the parameters before it, and
    `Self` in a method), in a trial whose code is dropped: a default is
    evaluated at each call that omits it, but it is the function's. So it
    neither fails nor suspends, even in a `<decides>` or `<suspends>`
    function, and has only the heap effects the function's own effects
    `allowed` allow (Book of Verse tests, `DefaultNamed.versetest` 805-878:
    3512). `ctx` is the context of the function's body, `st0` the state its
    elaboration starts from. -/
def checkParamDefaults (ctx : Ctx) (st0 : ESt) (name : String) (ps : List SParam) (ptys : List Ty)
    (allowed : List String) : Except String Unit := do
  for ((prm, t), i) in (ps.zip ptys).zipIdx do
    let some d := prm.default | continue
    let what := s!"the default of ?{prm.name} of {name}"
    -- (the parameters from this one on are not in its scope)
    let dctx := { ctx with
      locals := ctx.locals.filter fun l => !(i ≤ l.slot && l.slot < ps.length)
      canFail := false, suspends := false, inParamDefault := true, inLoop := false
      defaults := [(name, s!"?{prm.name}")] }
    let trial (exp : Option Ty) : EM Bool := do
      let r ← elabE dctx d exp
      return r.e.mayFail ctx.sigProg
    -- (at the parameter's type, or with none expected, where the default
    -- gives a type parameter nothing else determines its type, as at a
    -- call; a default that needs the type arguments of a call to be
    -- elaborated, or that is refused there, is left to its calls, which
    -- elaborate it as before)
    let suspends (msg : String) : Bool :=
      (msg.splitOn "suspends: it can only be").length > 1
    let outcome : Except String (Bool × ESt) := match (trial (some t)).run st0 with
      | .error msg => match (trial none).run st0 with
        | .error msg' => .error (if suspends msg then msg else msg')
        | ok => ok
      | ok => ok
    match outcome with
    | .ok (fails, st) =>
      if fails then
        throw s!"{d.pos.show}: {what} can fail: a default is no failure context, also of a <decides> function (Book of Verse tests, DefaultNamed.versetest)"
      fxCheck what allowed st
    | .error msg =>
      if suspends msg then
        throw s!"{msg}: {what} cannot suspend, also of a <suspends> function (Book of Verse tests, DefaultNamed.versetest)"

/-- Keep each actual Core signature's full call type. The metadata receiver
    projector binds generic parameters only from actual hidden witnesses;
    opaque binders never become caller-scope type certificates. -/
private def metadataReturns (signatures : List Sig) (count : Nat) : Array (Option MetadataReceivers.CallType) := Id.run do
  let mut types := Array.replicate count none
  let mut seen := Array.replicate count false
  for signature in signatures do
    if signature.idx < count then
      let frame := signature.frame
      let witnesses := (signature.tparams.filter fun (name, _) => !signature.selfTps.contains name).zipIdx.map
        fun ((name, _), index) => (name, frame.witnessBase + index)
      let candidate := if frame.valid then
        some ({ params := signature.params, ret := signature.ret, witnesses } : MetadataReceivers.CallType)
        else none
      if seen[signature.idx]! then
        -- A conflict is sticky: a later duplicate cannot resurrect a hint.
        if types[signature.idx]! != candidate then types := types.set! signature.idx none
      else
        seen := seen.set! signature.idx true
        types := types.set! signature.idx candidate
  return types

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
  /-- (#515) Its other calls, in a body whose effects exclude `no_rollback`
      (`ESt.bodyCalls`). -/
  bodyCalls : Array ((Pos × String) × List Nat) := #[]
  /-- The warnings its elaboration found (`ESt.warnings`). -/
  warnings : Array (Pos × String) := #[]
  /-- The slots of its source `var` locals (`ESt.sourceVars`, #724). -/
  sourceVars : List (Nat × String) := []

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
    (selfFieldOf : Option (String → Option Nat) := none)
    (evidenceSignature : Option Sig := none) (extendedDefaults : Bool := false)
    (callOnly : Bool := false) (fnReturns : Array (Option MetadataReceivers.CallType) := #[])
    (rollbackOnly : Bool := false) (bodyFailure : Bool := false) :
    Except String ElaboratedFn := do
  -- (#209) the values of `selfTps` come from the receiver's hidden
  -- fields, in slots after the hidden parameters: a method's own class's
  -- (`C.M`), or as `selfFieldOf` says (a cast's branch, #250, the cast
  -- target's, of the object, its first parameter too)
  let signature := evidenceSignature.getD {
    idx := 0, name, params := ptys, ret, decides, isConst := false, tparams := tps, selfTps,
    typeValues := ps.zipIdx.filterMap fun (param, i) => if param.typeValue then some i else none,
    metadataForwards := ps.zipIdx.filterMap fun (param, i) => if param.metadataForward then some i else none }
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
    rollbackOnly
    bodyFailure
    retTy := ret
    dictBase := frame.witnessBase
    suspends := suspends
    dictVars := dictTps.map (·.1) }
  let ctx ← functionBodyCtx requests base p name tps
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
  if !extendedDefaults then checkParamDefaults ctx st0 name ps ptys allowed
  if name.endsWith ".$block" then
    if let some budget := env.constructionFx[(name.dropEnd ".$block".length).toString]? then
      fxCheck s!"construction block of {(name.dropEnd ".$block".length).toString}" budget st
  let inputs := (locals.filter (·.typeValue)).map (·.slot) ++
    (List.range dictTps.length).map (frame.witnessBase + ·)
  -- Check executable inputs on emitted argument values in MetadataFlow. A
  -- source hint can taint an independent real return from an opaque helper.
  -- Keep the declaration's own domain, before substituting caller instances.
  let required := signature.params.zipIdx.filterMap fun (ty, i) =>
    if !signature.typeValues.contains i &&
        ((!signature.metadataForwards.contains i && SubtypeEvidence.exposesEvidence env ty) ||
        (i == 0 && ((signature.hasReceiver && !name.endsWith ".$block") ||
          ["$Await", "$EvAwait", "$StickyAwait", "$cancelMark"].contains name))) then some i else none
  let resume := requests.loops.findSome? fun l => l.resumes.find? (·.name == name)
  let forwarded ← (resume.toList.flatMap (·.forwarded)).mapM fun owner => do
    let args ← owner.args.mapM fun sty => do
      let (ty, _) ← (resolveTy env p sty).run {}
      pure (ty.toVTy env)
    pure ({ frame := owner.frame, name := owner.name, args } : FrameRefs.Origin)
  let frames : FrameRefs.Info := {
    explicit := ps.length, copies := st.frameCopies, forwarded, slots := st.frameSlots.map fun (i, s) =>
      (i, { frame := s.frame, name := s.name, args := s.args.map (Ty.toVTy env) }) }
  let cellTag := if env.classIx.isEmpty then
      if env.classes.contains "$varcell" then some (env.tagOf "$varcell") else none
    else env.classIx["$varcell"]?
  let transportTag := if env.classIx.isEmpty then
      if env.classes.contains "$lazycell" then some (env.tagOf "$lazycell") else none
    else env.classIx["$lazycell"]?
  let metadataBody := initPrefixE arity selfInits e
  let projected := if cellTag.isSome then MetadataReceivers.project env st.slotTys metadataBody fnReturns
    else { body := metadataBody }
  let metadata : MetadataFlow.Info := {
    pos := p, inputs, required, seeds := inputs ++ st.metadataSeeds, uses := st.metadataUses
    shared := st.frameSlots.map (·.1), metadataWrites := st.metadataWrites
    cellTag
    cellTransportTag := transportTag
    extraSlots := projected.extraSlots.size
    objectFreeSlots := if cellTag.isNone then [] else
      (st.slotTys ++ projected.extraSlots).toList.zipIdx.filterMap fun (ty, i) =>
        if MetadataValues.objectFree (ty.toVTy env) then some i else none
    cellParams := ptys.zipIdx.filterMap fun (ty, i) =>
      match ty with | .struct "$varcell" _ => some i | _ => none
    cellSlots := st.slotTys.toList.zipIdx.filterMap fun (ty, i) =>
      match ty with | .struct "$varcell" _ => some i | _ => none
    nonCellSlots := (if cellTag.isNone then [] else st.slotTys.toList.zipIdx.filterMap fun (ty, i) =>
      let disjoint := match ty with
        | .param .. | .any | .dyn => false
        | .struct owner _ => !env.isSub "$varcell" owner
        | _ => true
      if disjoint then some i else none) ++ projected.nonCellSlots
    cellHelper := callOnly || name.startsWith "$sourceLoopReturn"
    source := frames
    borrowTasks := defaultBridge name || choiceDefaultBridge name || requests.casts.any (·.name == name) ||
      resume.any (·.borrowTasks)
    body := some projected.body }
  return { fn := { name, arity, nslots := st.nslots, decides, writes := allowed.contains "writes",
                   body := initPrefixE arity inits e },
           slotTys := spawnParamTypes env name (st.slotTys.toList.map (Ty.toVTy env)), errAt := st.errAt,
           frames,
           needs := st.needs, loopFirst := st.loopFirst, failCalls := st.failCalls, bodyCalls := st.bodyCalls,
           warnings := st.warnings, metadata, sourceVars := st.sourceVars }

/-- Function elaboration, a phase of `elabProgramCore`: each function and
    constant of `sigs`, by index (a constant may not hold a mutable object, as
    it is computed at each use), then each generic function, once, with its
    type parameters opaque (`elabFn`; the defaults of their named parameters
    checked, `checkParamDefaults`, unless `Options.extendedDefaults`). -/
def elabFunctions (env : TyEnv) (sigs : Signatures) (requests : Requests)
    (extendedDefaults : Bool := false) :
    Except String (Array ElaboratedFn) := do
  let allSigs := sigs.all
  let fnReturns := metadataReturns allSigs sigs.prog.fns.length
  let genvOf (g : Sig) : TyEnv := g.typeEnv env
  -- FirstLift records the exact compiler-owned family materialized for a
  -- rewritten source consumer. Its original public source owner remains a
  -- root; these helpers are checked with that consumer's actual captures.
  let firstHelpers := requests.loops.foldl (fun names lift =>
    if !lift.name.startsWith "$first" then names else
      lift.extraFns.foldl (fun names top => match top with
        | .fn _ name .. => names.insert name ()
        | _ => names) (names.insert lift.name ())) ({} : Std.HashMap String Unit)
  -- (the functions, then the generic ones, by index)
  let mut elaborated : Array ElaboratedFn := #[]
  for (top, idx) in sigs.tops.zip (List.range sigs.tops.length) do
    let sig := sigs.sigs[idx]!
    match top with
    | .fn p n ps _ specs _ body =>
      elaborated := elaborated.push (← elabFn allSigs sigs.prog requests env p n ps sig.params sig.ret sig.decides sig.fx [] body sig.suspends
        (evidenceSignature := some sig) (extendedDefaults := extendedDefaults) (callOnly := firstHelpers.contains n) (fnReturns := fnReturns)
        (rollbackOnly := (SignalAdmission.excludesNoRollback n specs).isSome)
        (bodyFailure := sig.decides))
    | .const p n _ sty body =>
      -- a constant is computed at each use, so it would be a new object each
      -- time (until Verse Core has global state)
      if sig.ret.holdsMutable env then
        throw s!"{p.show}: the constant {n} would hold an object with var fields or of a <unique> class, which would be a new one at each use: make it a function"
      -- (#724) a module's constant is a data member: its definition calls
      -- no function that might not complete (Epic's error 3582), unless
      -- `--extended-defaults`
      let dataMember := if extendedDefaults || n.startsWith "$" then none
        else some s!"the value of the constant {n}"
      let ctx : Ctx := { sigs := allSigs, sigProg := sigs.prog, types := env, dataMember }
      let (r, st) ← elabBody ctx body (some sig.ret) { env }
      if let some msg := divergentCallError st.divergentCalls then throw msg
      let (e, st) ← (coerce p r.1 sig.ret).run st
      -- a module's constant has no side effect: its initializer writes
      -- nothing, also through what it calls or constructs ("all non-local
      -- variables initializers (module, instance) can't have side
      -- effects", the Book's tests, DefaultValueAssignment.versetest:199,
      -- ModuleDefinitions.versetest:278, ParametricTypes.versetest:465)
      -- (a type value is no construction: `Value:castable_subtype(c) = c`)
      -- (the front end writes metatypes as interfaces, `subtype(c)`, and a
      -- type value as the construction of a class of its own, `$type:c`:
      -- a constant of a type that has type values in it constructs none)
      let metatype := sty.any STy.mentionsMetatype
      if !n.startsWith "$" && !metatype then
        if let some (_, kp, via) := st.fx.find? (·.1 == "writes") then
          let what := match via with
            | some f => s!"{f}, which has the effect <writes>"
            | none => "sets a var field"
          -- (#724) UEFN 43.12's codes: a construction of a class without
          -- specifiers, 3512 (followup-3582/div-const-constructor); other
          -- side effects, 3582 (a call is refused as divergent before this,
          -- `divergentCallError`, unless `--extended-defaults`)
          let epic := if (via.map (·.startsWith "constructs")).getD false then
              "UEFN 43.12 refuses it with error 3512, \"This archetype instantiation constructs a class that has the 'transacts' effect, which is not allowed by its context\""
            else "UEFN 43.12 refuses it with error 3582, \"Expressions with side effects cannot be used when defining data-members\""
          throw s!"{kp.show}: the value of the constant {n} {what}: a module's constant has no side effect (Book of Verse tests, DefaultValueAssignment.versetest:199; {epic}); make it a function, or give it a value that writes nothing"
      -- slots start like a function's (a class-typed one as a placeholder)
      let inits ← match st.slotTys.toList.mapM (slotDefault env 0 [] []) with
        | .ok ds => pure ds
        | .error msg => throw s!"{p.show}: in {n}: {msg}"
      fxCheck n sig.fx st
      elaborated := elaborated.push {
        fn := { name := n, arity := 0, nslots := st.nslots, decides := false,
                writes := sig.fx.contains "writes", body := initPrefixE 0 inits e }
        slotTys := st.slotTys.toList.map (Ty.toVTy env), errAt := st.errAt, needs := st.needs,
        loopFirst := st.loopFirst, failCalls := st.failCalls, warnings := st.warnings
        sourceVars := st.sourceVars
        metadata := {
          pos := p, seeds := st.metadataSeeds, uses := st.metadataUses
          metadataWrites := st.metadataWrites, body := some e } }
    | .classDef .. => pure ()   -- expanded above
  -- (#724) a module constant that Epic's linker evaluates in 64 bits, and
  -- that leaves them, is refused (`ConstantRange`)
  let constBody (f : Nat) : Option Expr := match sigs.tops[f]?, elaborated[f]? with
    | some (.const _ n ..), some ef => if n.startsWith "$" then none else some ef.fn.body
    | _, _ => none
  for (top, idx) in sigs.tops.zip (List.range sigs.tops.length) do
    if let .const p n .. := top then
      if let some b := constBody idx then
        if let some what := ConstantRange.check constBody b then
          throw s!"{p.show}: the value of the module constant {n} leaves the 64-bit range when the module is evaluated ({what}): Epic's Verse compiler evaluates module constants with 64-bit ints and refuses this (error 9003, UEFN 43.12), though at run time ints go past 64 bits; compute it in a function"
  -- each generic function is elaborated once, with its type parameters
  -- opaque, as Verse checks it, into one Verse Core function whose types
  -- mention type variables; `Prog.checkTypes` checks it once, for every
  -- instantiation (`Typed.subst`)
  for (top, g) in sigs.generics.zip sigs.gsigs.toList do
    match top with
    | .fn p n ps _ specs _ body =>
      elaborated := elaborated.push (← elabFn allSigs sigs.prog requests (genvOf g) p n ps g.params g.ret g.decides g.fx g.tparams body
        g.suspends g.selfTps ((requests.casts.find? (·.name == n)).map fun l => fun v =>
          (l.opened.lookup v).bind (env.witnessField? l.target ·)) (some g) extendedDefaults (firstHelpers.contains n) fnReturns
        (SignalAdmission.excludesNoRollback n specs).isSome g.decides)
    | _ => pure ()
  return elaborated

end OpenVerse.Front
