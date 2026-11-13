/-
  OpenVerse front end — elaboration of surface Verse into Verse Core.

  * Names are resolved: locals to slots of the function's frame, functions
    and constants to program indices. Verse forbids shadowing; so does this.
  * Types are checked (int, logic, char, string = []char, []t, ?t, tuples,
    void), bidirectionally so that `false` and `array{}` take their type
    from context.
  * Failure discipline (Book of Verse ch. 8): an expression that can fail
    must be in a failure context — an `if` condition, a `for` clause,
    `option{}`, `logic{}`, `not`, the left of `or`, or a `<decides>`
    function body. "Can fail" is computed by `Expr.mayFail`, the very
    analysis the `<decides>` soundness theorem (`Eval.no_fail`) is about.
  * Derived forms use `OpenVerse.Core.Derived` (`not`, `or`, `option{}`,
    `logic{}`), whose rollback laws are proved.
  * The result is checked with `Prog.check` (proved to imply the hypotheses of
    the core theorems) before anyone runs it.
-/
import OpenVerse.Front.Elab.Environment
import OpenVerse.Front.Elab.Functions
import OpenVerse.Front.SignalAdmission
import OpenVerse.Front.InitializerConvergence

namespace OpenVerse.Front
open OpenVerse

/-- What an elaboration asks for (`Requests`, by tiers: `Requests.tier`): what
    its functions and the fields' defaults ask, and (#283) the families and
    overloads of the inlining's sites it did not reach (`Source`). -/
def roundNeeds (elaborated : Array ElaboratedFn) (fieldNeeds : Requests) (source : Source) : Requests := Id.run do
  let mut needs := elaborated.foldl (fun acc f => acc.merge f.needs) fieldNeeds
  if needs.families.isEmpty then needs := needs.merge { families := source.familySites.map fun (q, _) => (q, "") }
  if needs.overloads.isEmpty then needs := needs.merge { overloads := source.overloadSites.map fun (q, _) => (q, "") }
  return needs

/-- The function the program runs: `Main`, or with an entry expression its
    function `$Do`, which takes no parameters. -/
def mainSignature (sigs : Signatures) (entry : Option SExpr) : Except String Sig := do
  match sigs.sigs.toList.find? (·.name == (if entry.isSome then "$Do" else "Main")) with
  | some s =>
    if s.isConst || !s.params.isEmpty then throw "Main must be a function with no parameters"
    pure s
  | none => throw "the program has no Main() function"

/-- The functions of a program prepared for lowering (`prepareLowering`). -/
structure Lowering where
  /-- The functions, by index, then the accessors (#157). -/
  fns : Array Fn
  /-- Each function's slot types. -/
  slotTys : Array (List VTy)
  /-- What each function does with its type metadata (`MetadataFlow`). -/
  metadata : Array MetadataFlow.Info
  /-- Their signatures, the class table, the prototypes and the classes' pins. -/
  sigs : Sigs

/-- Preparation for lowering, a phase of `elabProgramCore`: the elaborated
    functions, then the accessors (#157), with their signatures, the class
    table (#34, #39), the prototypes (#37) and the pins (#142, #351); and the
    refined tests that can never pass removed (#186). -/
def prepareLowering (env : TyEnv) (sigs : Signatures) (elaborated : Array ElaboratedFn) : Lowering := Id.run do
  let genvOf (g : Sig) : TyEnv := g.typeEnv env
  let mut fns := elaborated.map (·.fn)
  let mut slotTys := elaborated.map (·.slotTys)
  let mut metadataInfo := elaborated.map (·.metadata)
  let fsigs0 := sigs.sigs.toList.map (fun s => (spawnParamTypes env s.name (s.params.map (Ty.toVTy env)), s.ret.toVTy env)) ++
    sigs.gsigs.toList.map fun g =>
      let genv := genvOf g
      (spawnParamTypes genv g.name (g.frame.argumentTypes.map (Ty.toVTy genv)), g.ret.toVTy genv)
  -- the class table: the fields of each class, by tag (#34); the prototypes (#37)
  -- (a parametric class's field types mention its type parameters, #39)
  -- each field as `TyEnv.fieldSrc` gives it (the topmost interface that
  -- declares it, else the topmost class in the chain that has it), in
  -- terms of the Verse Core type arguments the hierarchy shares: an
  -- `intbox := class(base(int))`'s inherited `Value` is `var 0`, as in `base`
  let classTable := env.classes.map fun d =>
    if env.isRefClass d then (env.fields d).map fun (f, t, _) =>
      (env.coreFieldTy d f).getD (t.toVTy { env with tvars := env.coreVars d })
    else []
  let protos := env.protos.map fun (d, t, _) => (t, (env.coreArgs d []).map (Ty.toVTy env))
  -- (a class below an interface referred to through views has pins on all of
  -- its Verse Core type arguments, so that a dispatch through a view opens
  -- them, `Typed.dispatch_view`, #351)
  let pins := env.classes.map fun d =>
    if env.isRefClass d then env.lowerPins (env.dispatchPins d) else []
  -- the accessors (#157): for each (class, field), `get(Self)` and
  -- `set(Self, V)`, generic over the class's type argument positions
  let mut accSigs : Array (List VTy × VTy) := #[]
  for (d, f) in env.fieldAcc do
    let tag := env.tagOf d
    let kd := ((fieldIndex (env.fields d) f).map (·.1)).getD 0
    let m := (env.coreArgs d (((env.sparams.lookup d).getD []).map fun (v, c) => Ty.param v c)).length
    let selfTy : VTy := .ref [tag] ((List.range m).map VTy.var)
    let fTy : VTy := ((classTable[tag]?).bind (·[kd]?)).getD .int
    fns := fns.push { name := s!"{d}.$get.{f}", arity := 1, nslots := 1, decides := false, writes := false,
                      body := .heap (.get kd) [.local 0] }
    slotTys := slotTys.push [selfTy]
    metadataInfo := metadataInfo.push {}
    accSigs := accSigs.push ([selfTy], fTy)
    fns := fns.push { name := s!"{d}.$set.{f}", arity := 2, nslots := 2, decides := false, writes := true,
                      body := .heap (.set kd) [.local 0, .local 1] }
    slotTys := slotTys.push [selfTy, fTy]
    metadataInfo := metadataInfo.push {
      metadataWrites := if f.startsWith "$w." then [(0, kd)] else [] }
    accSigs := accSigs.push ([selfTy, fTy], fTy)
  let fsigs0 := fsigs0 ++ accSigs.toList
  -- (a refined test, #142, of classes whose pins the receiver's closed type
  -- arguments rule out can never pass, and the checker types such a test
  -- only when the pins can agree: it goes, #186)
  let S00 : Sigs := { fns := fsigs0, classes := classTable, protos, pins }
  for gi in List.range fns.size do
    let fn := fns[gi]!
    fns := fns.set! gi { fn with body := Suspend.pruneDead S00 ((slotTys[gi]?).getD []) fn.body }
    metadataInfo := metadataInfo.modify gi fun info => { info with
      body := info.body.map (Suspend.pruneDead S00 ((slotTys[gi]?).getD [])) }
  return { fns, slotTys, metadata := metadataInfo, sigs := S00 }

/-- Initializer convergence (#511): each field default's code, `bodies`,
    converges, calling only functions that do (`InitializerConvergence`):
    those the source marks, the construction blocks of `cdefs` and the
    compiler's intrinsic operations `intrinsicCalls`. -/
def checkInitializerConvergence (fns : Array Fn) (sigs : Signatures) (cdefs : List CDef)
    (bodies : List (String × String × Pos × Expr)) (intrinsicCalls : List String) : Except String Unit := do
  let ordinary := (sigs.tops ++ sigs.generics).filterMap fun
    | .fn _ n _ _ specs .. =>
      if specs.contains InitializerConvergence.sourceCallMarker then some n else none
    | _ => none
  let construction := cdefs.filterMap fun cd =>
    if cd.methods.any (fun | .fn _ "$block" .. => true | _ => false) then
      some (cd.name ++ ".$block") else none
  let mut verified : Std.HashSet Nat := {}
  for (owner, field, pos, body) in bodies do
    match (InitializerConvergence.checkExpr fns ordinary (construction ++ intrinsicCalls) [] body).run verified with
    | .ok (_, checked) => verified := checked
    | .error reason =>
      throw s!"{pos.show}: default of field '{field}' of {owner} requires convergence: {reason} (#511; --extended-defaults retains the OpenVerse extension without a convergence assertion)"

/-- The hidden fields that hold type metadata (#209, `$w.`), of each class by
    its tag, for `MetadataFlow`. -/
def metadataFields (env : TyEnv) : Array (List Nat) :=
  env.classes.toArray.map fun c =>
    (env.fields c).zipIdx.filterMap fun ((name, _, _), i) =>
      if name.startsWith "$w." then some i else none

/-- A program as the lowering leaves it (`lowerProgram`), before `certify`:
    its Verse Core functions, their signatures with the class table, the
    prototypes and the classes' pins (`Sigs`), and each function's slot types. -/
structure LoweredProgram where
  prog : Prog
  sigs : Sigs
  slotTys : Array (List VTy)

/-- Lowering, a phase of `elabProgramCore`: failure capture (`FailCapture`);
    with concurrency (`usesConc`, #156), the suspends functions as frame
    classes and their functions (`lowerConcurrency`); and with prototypes or
    a suspends `Main`, a prelude `$Main` that allocates them and calls it
    (#37). -/
def lowerProgram (env : TyEnv) (sigs : Signatures) (mainSig : Sig) (lowering : Lowering)
    (frameInfo : Array FrameRefs.Info) (usesConc eventFifo : Bool) : Except String LoweredProgram := do
  let mut fns := lowering.fns
  let mut slotTys := lowering.slotTys
  let mut classTable := lowering.sigs.classes
  let protos := lowering.sigs.protos
  let pins := lowering.sigs.pins
  -- with prototypes, the program starts with a prelude that allocates them
  -- and then calls `Main` (#37)
  let mut protoList := env.protos.map fun (_, t, vs) => (t, vs)
  let mut frameClasses : Array (List VTy) := #[]
  let mut framePins : List (List (Option VTy)) := []
  let mut mainCall : Expr := .call mainSig.idx []
  -- (an error of the lowering names a function: with its position)
  let inFn := inFnMsg (sigs.tops ++ sigs.generics)
  let (capturedFns, capturedSlots, capturedSigs) ← FailCapture.lower fns slotTys lowering.sigs
  fns := capturedFns
  slotTys := capturedSlots
  let fsigs0 := capturedSigs.fns
  let mut fsigs := fsigs0
  -- concurrency (#156): each <suspends> function `g` becomes a frame class
  -- and the functions `g$new`, `g$reset` and `g$resume` (`Suspend.lean`);
  -- `g`'s own index is `g$resume`'s, as only suspends code calls it
  let beforeConcurrency := fns
  if usesConc then
    let (fns1, slotTys1, fsigs1, classTable1, frameClasses1, mainCall1, framePins1, schedMore) ←
      lowerOpening fun forced =>
        lowerConcurrency env sigs.sigs sigs.gsigs mainSig fsigs0 protos pins inFn fns slotTys fsigs classTable forced frameInfo
          eventFifo
    if !schedMore.isEmpty then
      let schedTag := env.tagOf "$sched"
      protoList := protoList.map fun (t, vs) => if t == schedTag then (t, vs ++ schedMore) else (t, vs)
    fns := fns1
    slotTys := slotTys1
    fsigs := fsigs1
    classTable := classTable1
    frameClasses := frameClasses1
    mainCall := mainCall1
    framePins := framePins1
  let mut main := mainSig.idx
  if !protoList.isEmpty || mainSig.suspends then
    main := fns.size
    fns := fns.push { name := "$Main", arity := 0, nslots := 0, decides := mainSig.decides,
                      writes := mainSig.fx.contains "writes" || mainSig.suspends,
                      body := protoPrelude protoList mainCall }
    slotTys := slotTys.push []
    fsigs := fsigs ++ [([], if mainSig.suspends then VTy.void else mainSig.ret.toVTy env)]
  if usesConc then
    fns := CompilerWrites.propagate beforeConcurrency fns
  -- (the frame classes' pins after the classes', #244)
  let pins := (List.range classTable.length).map (fun t => (pins[t]?).getD []) ++ framePins
  return { prog := { fns := fns.toList, main },
           sigs := { fns := fsigs, classes := classTable ++ frameClasses.toList, protos, pins }, slotTys }

/-- Certification, the last phase of `elabProgramCore`: the lowered program is
    given out with its certificate (`Compiled`) only if no call in it names a
    family's stub (#283), and it passes `Prog.check`, `Prog.checkControl` and
    `Prog.checkTypes` under its signatures and slot types. A program that does
    not is an elaborator bug, refused as an internal error that names what
    fails (with `debug`, the function's Verse Core too, for a bug report). -/
def certify (lowered : LoweredProgram) (stubs : List (String × Pos)) (debug : Bool) :
    Except String Compiled := do
  let P := lowered.prog
  let S := lowered.sigs
  let slotTys := lowered.slotTys
  -- (#283) no call names a family's stub (`Choice.familyStub`), whose body
  -- is `Err()`: each call of a method of the family was rewritten not to be
  -- one, and a stub has no value (`FnValues`). Verse Core has no calls but
  -- those naming their function (dispatch is a test of the class, then a
  -- call), so whatever code made them, no stub runs
  for fn in P.fns do
    for (g, _) in Suspend.callsOf fn.body do
      if let some q := (P.fns[g]?).bind fun callee => stubs.lookup callee.name then
        throw s!"{q.show}: {Choice.shownFnName P.fns[g]!.name} has several values, but a call of it in {Choice.shownFnName fn.name} is compiled as one of a method of one value, where its receiver's class was not known: not supported yet (#283)"
  if !P.check then
    let bad := P.fns.filter fun fn => (!fn.decides && fn.body.mayFail P) ||
      (!fn.writes && fn.body.writesHeap P) || !(fn.body.scoped P fn.nslots)
    throw s!"internal error: the elaborated program does not pass Prog.check ({bad.map (·.name)})"
  if !P.checkControl then throw "internal error: the elaborated program does not pass Prog.checkControl"
  if !P.checkTypes S slotTys.toList then
    -- name what fails, for a bug report
    let bad := (List.range P.fns.length).find? fun f =>
      match P.fns[f]?, S.fns[f]?, slotTys[f]? with
      | some fn, some (ps, τ), some Γ => !checkFn S fn ps τ Γ
      | _, _, _ => true
    let which := match bad with
      | some f =>
        -- (the innermost statement of its body the checker rejects, in sequence)
        let rec firstBad (fuel : Nat) (Γ : List VTy) (ρ : VTy) (e : Expr) : Expr :=
          match fuel, e with
          | f + 1, .seq a b =>
            if (tc S Γ ρ a none).isNone && (tc S Γ ρ a (some VTy.void)).isNone then firstBad f Γ ρ a
            else firstBad f Γ ρ b
          | _, e => e
        -- (first the slots' initial values, which `checkDefault` checks
        -- apart from the statements, then the body after them)
        let rec badInit (a k : Nat) (Γ : List VTy) : List VTy → Expr → Sum String Expr
          | [], e => .inr e
          | t :: ts, e => match e with
            | .seq (.assign i d) rest =>
              if i == k && checkDefault S a Γ d t then badInit a (k + 1) Γ ts rest
              else .inl s!"\n-- initial value of slot {k} rejected (type {repr t}): {d.compact}"
            | _ => .inl s!"\n-- no initial value for slot {k}"
        let badStmt : String := match P.fns[f]?, S.fns[f]?, slotTys[f]? with
          | some fn, some (_, τ), some Γ => match badInit fn.arity fn.arity Γ (Γ.drop fn.arity) fn.body with
            | .inl msg => msg
            | .inr b => s!"\n-- first rejected:\n{(firstBad 10000 Γ τ b).compact "   "}"
          | _, _, _ => ""
        let dump := if !debug then "" else
          badStmt ++ s!"\n-- body:\n{((P.fns[f]?).map (fun (fn : Fn) => fn.body.compact "   ")).getD "?"}\n-- arity: {(P.fns[f]?).map Fn.arity}" ++
          s!"\n-- slot types: {repr (slotTys[f]?)}\n-- signature: {repr (S.fns[f]?)}"
        s!" (in {((P.fns[f]?).map Fn.name).getD "?"}){dump}"
      | none => if !checkPrelude P S then " (the prototypes)" else ""
    throw s!"internal error: the elaborated program does not pass Prog.checkTypes{which}"
  return { prog := P, sigs := S, slotTys := slotTys.toList }

/-- Elaborate a parsed program into a Verse Core program that passes `Prog.check`
    and `Prog.checkTypes`, by its phases, in order (`docs/DESIGN.md`, "Elaboration
    in phases"); an elaboration that finds a need goes no further, and asks for
    it (`Compiled.asking`). -/
def elabProgramCore (allTops0r : List STop) (opts : Options := {}) : Except String Compiled := do
  let admitted ← admitSource allTops0r opts
  let source ← inlineSource allTops0r opts.requests admitted
  let defs ← argsAndMethodOverloads source.tops source.entry opts.args
  let classes ← classHierarchy defs.tops source.constructionFx
  let fields ← classFields classes opts.requests
  let methods ← classMethods defs.tops classes fields
  let env ← typeEnvironment classes fields methods source admitted.concurrencyNames opts.requests opts.signalNoRollback
  let env ← upperBounds env methods.tops
  let views ← interfaceViews env classes.defs opts.requests
  if !views.witnessNeeds.isEmpty then
    return .asking { witnesses := views.witnessNeeds }
  let env ← pinsAndAccessors { env with viewed := views.viewed } methods opts.requests
  let env ← addPlaceholders env
  let overloads ← functionOverloads env methods.tops defs.methodOverloads
  let env := { env with overloads := overloads.functions, methodOverloads := overloads.methods }
  let declared ← declareSignatures env overloads.tops opts.requests
  -- (the accessors come right after the functions, #157: known now, so that
  -- every elaboration from here on, field defaults' too, reads and sets a
  -- field through one at its place)
  let env := { env with fieldAccBase := declared.tops.length + declared.gsigs.size }
  let sigs ← inferSignatures env declared admitted.typeDefaults opts.requests
  checkSignatures env sigs classes.defs fields methods
  let defaults ← elabFieldDefaults env sigs methods.tops classes.defs
  let elaborated ← elabFunctions env sigs opts.requests
  let needs := roundNeeds elaborated defaults.needs source
  -- (#283) the eager groups, the families of the uses of methods whose
  -- receivers' classes this one found, and the overloads of the calls whose
  -- arguments' types it found; those it did not reach, of no family or
  -- overload, so that the last elaboration has none to find (and knows what
  -- can fail): the program is elaborated again with them, so this one goes
  -- no further
  -- (and the types of the names of consumers in recursive groups' code,
  -- whose groups this one kept with one value: `$noteTypes`)
  -- (and the field orders of the structs and classes those groups construct
  -- with a choice point in a field, `TyEnv.fieldOrder`)
  if !needs.eager.isEmpty || !needs.families.isEmpty || !needs.overloads.isEmpty || !source.nestedSites.isEmpty ||
      !source.fieldSites.isEmpty then
    return .asking { eager := needs.eager, families := needs.families, overloads := needs.overloads,
                     nested := needs.nested, fieldOrders := source.fieldSites.map fun n => (n, env.fieldOrder n) }
  -- (#214) and functions wanted as values at types no class of theirs
  -- gives, adapters for methods wanted as values, (#243) branches of casts
  -- that refine type arguments, lifted into functions, and helpers that
  -- forward calls to the defaults of their named parameters: likewise, as
  -- this one has placeholders for them
  if !needs.isEmpty then return .asking needs
  let mainSig ← mainSignature sigs opts.entry
  let lowering := prepareLowering env sigs elaborated
  -- (where each function calls `Err()`, by its index, #235)
  let errs := elaborated.map (·.errAt)
  -- (#235) the functions with several values computed at their calls
  let lazyNeeds ← checkEager lowering.fns errs (fun g => ((sigs.tops ++ sigs.generics).findSome? fun
    | .fn p n .. => if n == g then some p else none
    | _ => none)) opts.requests.lazy
  if !lazyNeeds.isEmpty then
    return .asking { lazy := lazyNeeds }
  let failCalls := elaborated.foldl (fun acc f => acc ++ f.failCalls) #[]
  -- (#515, `--signal-no-rollback`) no event signal from a failure context
  if opts.signalNoRollback then
    if let some ((p, what), way) := SignalAdmission.checkSites lowering.fns failCalls then
      throw s!"{p.show}: this {what} may signal an event ({" → ".intercalate way}) in a failure context, which --signal-no-rollback refuses: the published Verse API makes an event's Signal <no_rollback> (#515)"
  -- (the lazily taken functions with several values that contexts taking
  -- their first success consume, #246)
  let loopFirst := elaborated.toList.flatMap (·.loopFirst)
  -- (#246) and functions of their own for the lazily taken calls whose
  -- effects need them: the program is elaborated again, with them
  let loopNeeds ← checkLoopFirst lowering.fns loopFirst opts.requests.loops
  if !loopNeeds.isEmpty then
    return .asking { loops := loopNeeds }
  if !opts.extendedDefaults then
    checkInitializerConvergence lowering.fns sigs classes.defs defaults.bodies admitted.intrinsicCalls
  MetadataFlow.check lowering.fns lowering.metadata (metadataFields env) opts.debug
  let frameInfo := elaborated.map (·.frames)
  certify (← lowerProgram env sigs mainSig lowering frameInfo admitted.usesConc opts.eventFifo) methods.stubs
    opts.debug

/-- `F$ovN` (an overload, #74) shown as `F`: every `$ov` and the digits after it removed. -/
def stripOv (msg0 : String) : String := Id.run do
  -- `K$default$F` (a default an overloaded constructor fills in) is "the default of F"
  let msg := match msg0.splitOn "$default$" with
    | [] | [_] => msg0
    | first :: rest =>
      let dropName (x : String) : String :=
        String.ofList (x.toList.reverse.dropWhile (fun (c : Char) => c.isAlphanum || c == '_')).reverse
      rest.foldl (fun acc part => dropName acc ++ "the default of " ++ part) first
  -- (an array: a list's indexing and length are linear, which made this
  -- quadratic in the message, minutes for `OPENVERSE_DEBUG`'s dump)
  let cs := msg.toList.toArray
  let mut out : String := ""
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '$' && i + 2 < cs.size && cs[i+1]! == 'o' && cs[i+2]! == 'v' then
      i := i + 3
      while i < cs.size && cs[i]!.isDigit do i := i + 1
    else
      out := out.push cs[i]!
      i := i + 1
  return out

/-- Nested consumers can discover a continuation and its refining branches
    in separate rounds. Bound discovery by source nesting, rather than a
    fixed four rounds; every round must still add a new request. -/
partial def liftDepth (e : SExpr) : Nat :=
  1 + e.children.foldl (fun n child => max n (liftDepth child)) 0

partial def topLiftDepth : STop → Nat
  | .fn _ _ ps _ _ _ body =>
    (ps.filterMap (·.default)).foldl (fun n e => max n (liftDepth e)) (liftDepth body)
  | .const _ _ _ e => liftDepth e
  | .classDef _ _ _ _ _ _ fields _ methods =>
    methods.foldl (fun n t => max n (topLiftDepth t))
      (fields.foldl (fun n (_, _, e, _) => max n (e.map liftDepth |>.getD 0)) 0)

/-- Named defaults can discover forwarding helpers along a dependency
    chain. Interface copies may instantiate each source method per class. -/
partial def topDefaultCount : STop → Nat
  | .fn _ _ ps _ _ _ _ => (ps.filter (·.named)).length
  | .classDef _ _ _ _ _ _ _ _ ms => ms.foldl (fun n m => n + topDefaultCount m) 0
  | _ => 0

/-- What an elaboration asks for (`Requests`) is of three tiers, by what it
    changes, and an elaboration asks for one tier at a time
    (`elabProgramCore` goes no further than the first it finds):
    1. how the source's choices are inlined (#283): eager groups, lazily
       taken functions, the families of methods' uses, the overloads of
       calls, the types of consumers' names in recursive groups' code and
       the field orders of what that code constructs;
    2. the classes' layout (#351): hidden fields for all of a class's type
       parameters;
    3. the functions added: functions as values (#214), method adapters, the
       branches of refining casts (#243), and the functions of lazily taken
       calls and the helpers of consumers of choices (#246, #335). -/
def Requests.tier (r : Requests) : Nat :=
  if !r.eager.isEmpty || !r.families.isEmpty || !r.overloads.isEmpty || !r.lazy.isEmpty || !r.nested.isEmpty ||
      !r.fieldOrders.isEmpty then 1
  else if !r.witnesses.isEmpty then 2
  else 3

/-- The requests of tier `k` and of the tiers above it (`Requests.tier`). -/
def Requests.upTo (r : Requests) (k : Nat) : Requests :=
  if k ≥ 3 then r else
  { eager := r.eager, families := r.families, overloads := r.overloads, lazy := r.lazy, nested := r.nested,
    fieldOrders := r.fieldOrders, witnesses := if k = 2 then r.witnesses else [] }

/-- Elaborate a parsed program (`elabProgramCore`), with the names of the
    functions a constructor or an overload becomes shown as written: `K$init`
    is `K<constructor>`, `F$ov1` is `F` (names with `$` are never the user's).

    It is elaborated in rounds: as long as an elaboration asks for something
    new, the program is elaborated again with it. A round that asks for more
    of one tier (`Requests.tier`) is followed by one with the requests of that
    tier and of the tiers above it only, as what the source or the classes
    are changes what the tiers below ask for: those are asked for again, and
    their budgets of rounds start again. -/
def elabProgram (allTops00 : List STop) (opts : Options := {}) : Except String Compiled :=
  let defaults := allTops00.foldl (fun n t => n + topDefaultCount t) 0
  let classes := allTops00.filter (fun | .classDef .. => true | _ => false) |>.length
  -- (tier 3: each round asks for new functions only, so a few rounds do)
  let rounds := max 4 (4 * (allTops00.foldl (fun n t => max n (topLiftDepth t)) 0 + defaults * (classes + 1)))
  -- (tier 2: each round asks for more classes' hidden fields)
  let witnessRounds := max 8 (classes + 1)
  -- (tier 1: each round notes the uses of methods it found, which may make
  -- more methods have several values, whose uses the next one notes. A
  -- restart discards helpers prepared for the lazy group; their bodies
  -- must be discovered again after its calls become eager. Each restart
  -- forces a new source function's group, so source definitions bound it.)
  let eagerRounds := allTops00.foldl (fun n t => n + match t with
    | .fn .. => 1
    | .classDef _ _ _ _ _ _ _ _ ms => ms.length
    | _ => 0) 1
  let rec loop (eagerFuel witnessFuel fuel : Nat) (req : Requests) : Except String Compiled := do
    let c ← elabProgramCore allTops00 { opts with requests := req }
    let new := c.needs.without req
    match c.needs.tier with
    | 1 =>
      match eagerFuel, new.isEmpty with
      | eagerFuel + 1, false => loop eagerFuel witnessRounds rounds ((req.upTo 1).merge new)
      | _, _ => throw "internal error: mutual generator instances or methods' families still changing after eager lowering (#283)"
    | 2 =>
      match witnessFuel with
      | witnessFuel + 1 => loop eagerFuel witnessFuel rounds ((req.upTo 2).merge new)
      | 0 => throw "internal error: classes still asking for hidden fields after several elaborations (#351)"
    | _ =>
      if new.isEmpty then
        if c.needs.isEmpty then return c
        -- (all asked for before: an elaboration asks for functions and
        -- methods only when they are not requested yet, and one that asks
        -- for anything has no program, `Compiled.asking`)
        if fuel == 0 then
          throw "internal error: casts that refine type arguments, or lazily taken calls, still to lift after several elaborations (#243, #246)"
        throw "internal error: a function as a value, a method adapter, a cast that refines type arguments, or a lazily taken call's function was asked for again (#214, #243, #246)"
      let newDefaults := new.loops.filter fun l => defaultBridge l.name
      match fuel with
      | 0 =>
        if !newDefaults.isEmpty then throw "internal error: default forwarding helpers still to infer after several elaborations"
        if !new.methods.isEmpty then throw "internal error: method variance adapters still to infer after several elaborations"
        -- (a program with a placeholder left is never given out)
        if !new.fns.isEmpty then throw "internal error: functions still wanted as values after several elaborations (#214)"
        throw "internal error: casts that refine type arguments, or lazily taken calls, still to lift after several elaborations (#243, #246)"
      | fuel + 1 =>
        if newDefaults.isEmpty then return ← loop eagerFuel witnessFuel fuel (req.merge new)
        -- A newly materialized dispatch-default helper can reveal heap effects
        -- absent from an earlier suffix trial. Rediscover consumers after those
        -- helpers have participated in effect inference; their cached stage
        -- interfaces, prefixes and resume methods must agree on permissions.
        -- Each restart retains the new bridges, so discovery still progresses.
        let bridges := req.loops.filter fun l => defaultBridge l.name || spawnAdapter l.name
        loop eagerFuel witnessFuel fuel { req.merge { fns := new.fns, methods := new.methods, subtypes := new.subtypes } with
          casts := [], loops := bridges ++ newDefaults }
  termination_by (eagerFuel, witnessFuel, fuel)
  (loop eagerRounds witnessRounds rounds opts.requests).mapError fun msg =>
    FnValues.pretty (((stripOv ((Refine.unmarked msg).replace "$init" "<constructor>")).replace "::" ".").replace "$replaceAll" "ReplaceAll")

/-- Parse and elaborate Verse source text. -/
def compileChecked (src : String) (opts : Options := {}) : Except String Compiled := do
  elabProgram (← parseProgram src) opts

/-- Parse and elaborate Verse source text. -/
def compile (src : String) (opts : Options := {}) : Except String Prog := do
  return (← compileChecked src opts).prog

/-- Compile loaded definitions (`Front.loadProgram`) with shell arguments,
    bound to `Args` when given or mentioned, and an optional `do` expression. -/
def compileTops (tops : List STop) (args : List String) (mentionsArgs : Bool) (doExpr : Option String)
    (debug : Bool := false) (profile : SourceProfile := .full) (eventFifo : Bool := false)
    (extendedDefaults : Bool := false) (signalNoRollback : Bool := false) : Except String Prog := do
  let entry ← match doExpr with
    | some t => some <$> parseExprText t
    | none => pure none
  let useArgs := !args.isEmpty || mentionsArgs
  let opts : Options := { args := if useArgs then some args else none, entry, debug, profile, eventFifo, extendedDefaults }
  return (← elabProgram tops { opts with signalNoRollback }).prog

/-- Compile with shell arguments (bound to `Args` when given or used) and an
    optional `do` expression, as `openverse run FILE ARG… do EXPR` does. -/
def compileWith (src : String) (args : List String) (doExpr : Option String)
    (profile : SourceProfile := .full) (extendedDefaults : Bool := false) : Except String Prog := do
  let entry ← match doExpr with
    | some t => some <$> parseExprText t
    | none => pure none
  let useArgs := !args.isEmpty || (src.splitOn "Args").length > 1
  compile src { args := if useArgs then some args else none, entry, profile, extendedDefaults }

end OpenVerse.Front
