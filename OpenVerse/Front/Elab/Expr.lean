/- Elaboration expr; public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Application
import OpenVerse.Front.Elab.Statement
import OpenVerse.Front.Elab.ExpressionControl
import OpenVerse.Front.Elab.ExpressionValues
import OpenVerse.Front.Elab.ExpressionMarkers
import OpenVerse.Front.Elab.ExpressionInitial

namespace OpenVerse.Front
open OpenVerse
set_option maxHeartbeats 800000 in
mutual
partial def choiceCoerceResult (ctx : Ctx) (p : Pos) (r : R) (exp : Option Ty) : EM R := do
  let some target := exp | return r
  if r.ty == target then return r
  let some (dictionary, source, _) := ctx.choiceCoercions.find? (fun (_, source, destination) =>
    r.ty == source && target == destination) | return r
  if ctx.typeOnly then return ⟨.seq r.e (.prim .userErr []), target⟩
  let slot ← fresh source
  let savedName := s!"$choiceConversionValue{slot}"
  let inner := { ctx with
    locals := { name := savedName, slot, ty := source, mutable := false } :: dictionary :: ctx.locals }
  let invocation := SExpr.app p (.ident p "$choiceOperation")
    [.str p [.text (FnValues.shapeOf 1 ["computes"]).name], .ident p dictionary.name, .ident p savedName] false
  let converted ← elabECore inner invocation (some target)
  return ⟨.seq (.assign slot r.e) converted.e, converted.ty⟩

partial def elabE (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  let ctx := ctx.choiceCoercionScope
  let result ← elabECore ctx se exp
  let result ← choiceCoerceResult ctx se.pos result exp
  -- Dataflow propagates roles through ordinary expressions. Only metadata
  -- origins need a marker; wrapping forwarding/control expressions can
  -- change the saved-local shape required by refinement copy-out.
  let origin := match se with
    | .ident _ name => name == "$witness"
    | .member _ _ field => field.startsWith "$w."
    | .app _ (.ident _ name) _ false => ["$typeValue", "$witness", "$stageWitness"].contains name
    | _ => false
  if ctx.typeOnly || !origin || result.ty == .never || result.ty == .void then return result
  if let .ident .. := se then
    if let .local slot := result.e then
      modify fun st => { st with metadataSeeds := slot :: st.metadataSeeds }
      return result
  -- A wrapper can mark an otherwise real local as metadata. Give that
  -- occurrence its own slot; never change the original local's role.
  let slot ← fresh result.ty
  modify fun st => { st with metadataSeeds := slot :: st.metadataSeeds }
  return ⟨.assign slot result.e, result.ty⟩

partial def elabECore (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  let result ← elabERaw ctx se exp
  if let some target := exp then
    if target != .void && result.ty != target && result.ty != .never &&
        (!result.ty.params.isEmpty || !target.params.isEmpty) then
      let locals := ctx.evidenceTypes
      if let some plan := SubtypeEvidence.find? ctx.types locals ⟨target, result.ty⟩ then
        if plan.usesLocal then return ← elabSubtypeUp ctx se.pos result target plan
  return result

partial def elabSubtypeUp (ctx : Ctx) (p : Pos) (value : R) (target : Ty)
    (plan : SubtypeEvidence.Plan) : EM R :=
  elabSubtypeUpWith elabE ctx p value target plan

partial def elabBoundReceiver (ctx : Ctx) (p : Pos) (value : R) (member : String) : EM R :=
  elabBoundReceiverWith elabE ctx p value member

partial def elabCallableReceiver (ctx : Ctx) (p : Pos) (value : R) : EM R := do
  let view ← match ctx.callableView p value.ty with
    | .ok view => pure view
    | .error message => throw message
  let some target := view | return value
  if target == value.ty then return value
  let some plan := SubtypeEvidence.find? ctx.types ctx.evidenceTypes ⟨target, value.ty⟩
    | eerr p "internal: a callable bound lost its lexical dictionary"
  elabSubtypeUp ctx p value target plan

partial def elabReceiverEvidence (ctx : Ctx) (p : Pos)
    (frame : SubtypeEvidence.Frame) : EM (List Expr) :=
  frame.receiverBounds.mapM fun (_, bound, field) => do
    let some receiver := frame.explicit.head? | eerr p "internal: receiver evidence has no receiver"
    let .struct owner args := receiver | eerr p "internal: receiver evidence needs a class"
    if !ctx.types.isRefClass owner then eerr p "internal: receiver evidence needs a reference class"
    let some (fieldName, fieldTy, _) := (ctx.types.fields owner args)[field]?
      | eerr p "internal: receiver evidence field is missing"
    if !fieldName.startsWith SubtypeEvidence.fieldPrefix || ctx.types.isVarField owner fieldName || fieldTy != bound.ty then
      eerr p "internal: receiver evidence field has the wrong type"
    coerce p (← elabMember ctx p ⟨.local 0, receiver⟩ fieldName) bound.ty

partial def elabERaw (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  if !ctx.constructProbe && ctx.constructHints.isNone &&
      Choice.anyE (fun
        | e@(.construct _ n [] _) =>
          !((ctx.types.sparams.lookup n).getD []).isEmpty && Choice.hasLiftable e
        | _ => false) se then
    let st0 ← get
    discard <| elabE { ctx with constructProbe := true, typeOnly := true, constructOrigin := some ctx.frameName } se exp
    let hints := (← get).constructHints
    set st0
    return ← elabE { ctx with constructHints := some hints, constructOrigin := some ctx.frameName } se exp
  -- Keep this constructor match exhaustive; only applications cross stage fallthroughs.
  match se with
  | .int .. | .char .. | .char32 .. | .float .. | .str .. | .ident .. | .app .. =>
    elabExprInitialWith elabE elabOneClauses elabSpawnBound elabFieldDefault elabConstruct elabExprMarkers ctx se exp
  | .member .. | .construct .. | .mapLit .. | .structDef .. | .enumDef .. | .refineDef .. | .query .. | .neg .. | .notE .. | .bin .. | .cmp .. | .andE .. | .orE .. | .range .. | .tuple .. | .block .. | .arrayLit .. | .optionLit .. | .logicLit .. =>
    elabExprValues ctx se exp
  | .ite .. | .forE .. | .gen .. | .loop .. | .brk .. | .ret .. | .caseE .. | .decl .. | .set .. =>
    elabExprControl ctx se exp

partial def elabExprMarkers (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R :=
  elabExprMarkersWith elabE elabRefineExit (@elabConc) elabSpawn elabBranch elabApp (@elabFor) elabOneClauses elabFirstGo elabExprValues ctx se exp

partial def elabExprValues (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R :=
  elabExprValuesWith elabE (elabSeqIn true) elabApp ratCall elabCmp (@elabMember) elabConstruct elabMapLit ctx se exp

partial def elabExprControl (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R :=
  elabExprControlWith elabE elabStmt elabDefers elabRefineExit elabSeq (@elabRefinedIf) refinedIfType elabSet (@elabFor) elabOneClauses elabCase ctx se exp

partial def elabStmt (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM (R × Ctx) :=
  elabStmtWith elabE ctx se exp

/-- `defer:` bodies, run in order (innermost first): each cannot fail, return
    or break out of itself, and sees the locals in scope where it is
    registered (Verse has no shadowing, so those at an exit include them). -/
partial def elabDefers (ctx : Ctx) (ds : List (SExpr × List Local)) : EM Expr := do
  elabDefersCore ctx ds

/-- Save the source return operand, unwind the lifted branch, then pack
    the exit flags and updated locals for its caller. -/
partial def elabRefineExit (ctx : Ctx) (p : Pos) (pre pack : List SExpr) : EM R := do
  if ctx.defers.isEmpty then
    let r ← elabE ctx (.block p (pre ++ pack)) (some ctx.retTy)
    return ⟨.ret (← coerce p r ctx.retTy), .never⟩
  let (r, c) ← elabSeq ctx pre none
  -- (a `break`'s target is its loop; a `return`'s caller passes `false`)
  let ds ← elabDefers (ctx.exitDefers ctx.loopRollback) ctx.defers
  let out ← elabE { c with defers := [] } (.block p pack) (some ctx.retTy)
  let e := Expr.seq ds (.ret (← coerce p out ctx.retTy))
  return ⟨if pre.isEmpty then e else .seq r.e e, .never⟩

/-- A suspension point with the code of the `defer:` blocks active there, in
    a branch that never runs (`if (false) …`), for the lowering's
    cancellation (#156): the defers run when a cancelled task unwinds. -/
partial def withDeferMark (ctx : Ctx) (e : Expr) : EM Expr := do
  if ctx.defers.isEmpty then return e
  -- (a cancelled task's unwinding: never in a failure context, #515)
  return .seq (.ite (.prim .fail []) (← elabDefersCore (ctx.exitDefers false) ctx.defers) (.lit .void)) e

/-- `sync:` (`isSync`) or `race:` with arms `arms` (#156): each arm's value
    goes to a slot (`race`: one slot of the arms' join type, written by the
    winner), and the arms to the marker `$syncMark(array{…})` (or
    `$raceMark`), which the lowering (`Suspend.lean`) runs concurrently. -/
partial def elabConc (ctx : Ctx) (p : Pos) (isSync : Bool) (arms : List SExpr) (exp : Option Ty)
    (isRush : Bool := false) : EM R := do
  let kw := if isSync then "sync" else if isRush then "rush" else "race"
  if !ctx.suspends then eerr p s!"{kw} suspends: it can only be used in a <suspends> function (#156)"
  if ctx.inDefer then eerr p s!"{kw} suspends, and a defer cannot suspend (#156)"
  if ctx.canFail then eerr p s!"{kw} suspends, and a failure context (a condition, a filter, or a <decides> call's arguments) cannot (#156)"
  if isRush && ctx.inRepeat then
    eerr p "rush cannot be in a loop or for body (Book of Verse ch. 14): call a function that rushes"
  let some mark := ctx.sig? (if isSync then "$syncMark" else if isRush then "$rushMark" else "$raceMark")
    | eerr p s!"internal error: no {kw} helper"
  -- (an arm is a scope of its own: its defers are its own, and break and
  -- return cannot leave it)
  let armCtx := { ctx with defers := [], loopDefers := 0, inLoop := false, inArm := true }
  if isSync then
    let mut stmts : Array Expr := #[]
    let mut slots : Array Nat := #[]
    let mut tys : Array Ty := #[]
    let mut async := 0
    -- (an expected tuple type gives each arm its expected type)
    let armExp : List (Option Ty) := match exp with
      | some (.tup ts) => if ts.length == arms.length then ts.map some else arms.map fun _ => none
      | _ => arms.map fun _ => none
    for (a, ae) in arms.zip armExp do
      let sourceBefore := (← get).pendingSourceSuspends
      let r ← elabE armCtx a ae
      let r ← match ae with
        | some t => pure ⟨← coerce a.pos r t, t⟩
        | none => pure r
      -- (a spawn or a branch in an arm does not make it wait)
      if sourceBefore != (← get).pendingSourceSuspends || ctx.sourceWaits r.e then async := async + 1
      let ty := if r.ty == .never then Ty.void else r.ty
      let t ← fresh ty
      stmts := stmts.push (.seq (.assign t r.e) (.lit .void))
      slots := slots.push t
      tys := tys.push ty
    if async < 2 then
      eerr p "sync needs at least two arms that can suspend (Book of Verse ch. 14): write the others in sequence"
    let e := Expr.seq (.call mark.idx [.prim .mkArr stmts.toList]) (.prim .mkTup (slots.toList.map Expr.local))
    return ⟨← withDeferMark ctx e, .tup tys.toList⟩
  else
    if arms.length < 2 then eerr p s!"{kw} needs at least two arms"
    -- the arms' join, as an `if`'s branches (or the expected type)
    let mut rs : Array (Pos × R) := #[]
    for a in arms do
      rs := rs.push (a.pos, ← elabE armCtx a exp)
    if isRush then
      noteBackgroundCaptures ctx (rs.toList.flatMap fun (_, r) => Suspend.slotsOf r.e)
    -- (as an `if`'s branches: void when one is, `any` when nothing else is
    -- common)
    let mut ty : Ty := .never
    for (_, r) in rs.toList do
      ty ← join p ty r.ty exp
    let rty := match exp with
      | some t => t
      | none => ty
    let t ← fresh rty
    let mut stmts : Array Expr := #[]
    for (ap, r) in rs do
      stmts := stmts.push (.seq (.assign t (← coerce ap r rty)) (.lit .void))
    let e := Expr.seq (.call mark.idx [.prim .mkArr stmts.toList]) (.local t)
    return ⟨← withDeferMark ctx e, rty⟩

/-- `spawn{F(…)}` (#156): a new task running the call, which must be of a
    `<suspends>` function; its arguments are evaluated now. The value is
    the task, a `task(t)`. The lowering (`Suspend.lean`) turns the marker
    `$spawnMark(array{F(…), T})` into a new task root. -/
partial def elabSpawn (ctx : Ctx) (p : Pos) (body : SExpr) : EM R := do
  -- (#515: the task runs the call later, outside a failure context the
  -- `spawn` is in; its arguments, evaluated now, are recorded here)
  let r ← elabSpawnIn { ctx with inRollback := false } p body
  noteFailCalls ctx p "spawn's arguments" r.e
  return r

partial def elabSpawnIn (ctx : Ctx) (p : Pos) (body : SExpr) : EM R := do
  let sourceBefore := (← get).pendingSourceSuspends
  if ctx.inDefer then eerr p "spawn in a defer is not supported (#156)"
  if ctx.canFail && !ctx.inDefaultCheck then
    eerr p "spawn cannot be in a failure context (a condition, a filter, or a <decides> call's arguments) (#156)"
  let some mark := ctx.sig? "$spawnMark"
    | eerr p "spawn{…} takes a call of a <suspends> function (#156)"
  let call := match body with
    | .block _ [e] => e
    | e => e
  if let .app q (.member mp obj m0) args br := call then
    let isSuper := match obj with | .ident _ "(super:)" => true | _ => false
    if !isSuper then
      let saved ← get
      let rx ← elabE { ctx with defers := [], suspends := true, canFail := false } obj none
      if let .struct c _ := rx.ty then
        let (owner, m) := if m0.startsWith "(" then
          match (m0.drop 1).toString.splitOn ":)" with
          | [owner, m] => (owner, m)
          | _ => (c, m0)
          else (c, m0)
        let method := (ctx.methodDecl? owner m).isSome ||
          ((ctx.types.methodOverloads.lookup m).getD []).any fun o => (ctx.methodDecl? owner o).isSome
        if ctx.types.classes.contains c && method then
          let isS (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.suspends
          if Suspend.countSusp isS (fun _ => false) false (· == mark.idx) rx.e > 0 then
            eerr p "the arguments of a spawned call cannot suspend (#156)"
          let slot ← fresh rx.ty
          let name := s!"$spawnReceiver{slot}"
          let cctx := { ctx with locals := {
            name, slot, ty := rx.ty, mutable := false, typeValue := ctx.isTypeValue obj } :: ctx.locals }
          let r ← elabApp { cctx with defers := [], suspends := true, canFail := false } q
            (.member mp (.ident mp name) ("$spawnMethod:" ++ m0)) args br none
          modify fun st => { st with pendingSourceSuspends := sourceBefore }
          return ⟨.seq (.assign slot rx.e) r.e, r.ty⟩
      set saved
  -- Function values use their interface's spawn dispatch, including fields
  -- and returned values. That path remains typed when a requested adapter
  -- has not been generated yet. Save the value once before its arguments.
  if let .app q f args br := call then
    let value := match f with
      | .ident _ n => (ctx.lookup n).isSome || ctx.selfClass.any (fun c =>
          (ctx.types.fields c).any (·.1 == n))
      | _ => true
    if value then
      let saved ← get
      let rx? ← tryCatch (do
        let value ← elabE { ctx with defers := [], suspends := true, canFail := false } f none
        some <$> elabCallableReceiver ctx f.pos value)
        (fun _ => pure none)
      if let some rx := rx? then
        if let .struct shape _ := rx.ty then
          if (FnValues.parseName shape).isSome then
            if !ctx.typeOnly && ctx.isTypeValue f then
              eerr f.pos "dummy type value cannot be an executable function"
            let isS (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.suspends
            if Suspend.countSusp isS (fun _ => false) false (· == mark.idx) rx.e > 0 then
              eerr p "the arguments of a spawned call cannot suspend (#156)"
            let slot ← fresh rx.ty
            let name := s!"$spawnValue{slot}"
            let cctx := { ctx with locals := {
              name, slot, ty := rx.ty, mutable := false, typeValue := ctx.isTypeValue f } :: ctx.locals }
            let r ← elabApp { cctx with defers := [], suspends := true, canFail := false } q
              (.member f.pos (.ident f.pos name) ("$spawnMethod:" ++ FnValues.callOf shape)) args br none
            return ⟨.seq (.assign slot rx.e) r.e, r.ty⟩
      set saved
  -- (the call runs in the new task, which may wait, also when spawned from
  -- an immediate function; its arguments may not)
  let r ← elabE { ctx with defers := [], suspends := true, canFail := false } call none
  let isS : Nat → Bool := fun f => ctx.sigs.any fun s => s.idx == f && s.suspends
  let e := match r.e with
    | .seq (.ite (.prim .fail []) _ (.lit .void)) e => e
    | e => e
  -- (statements before the call, such as a method call's receiver, run
  -- now, as the arguments are evaluated)
  -- (a method with several implementations: the dispatch on the
  -- receiver's class, a chain of tests that the lowering makes a function
  -- of the slots it uses, #173)
  let rec peel : Expr → Option (List Expr × Expr)
    | .call g es => some ([], .call g es)
    | .seq a b => (peel b).map fun (ps, c) => (a :: ps, c)
    | e@(.ite ..) => if Suspend.isDispatchChain e then some ([], e) else none
    -- (one refined by #142, through a temporary of the result type)
    | .assign _ e@(.ite ..) => if Suspend.isDispatchChain e then some ([], e) else none
    | _ => none
  let some (pre, callE) := peel e
    | eerr p "spawn{…} takes one call of a <suspends> function or method, with its arguments (#156)"
  let dispatch := match callE with | .assign _ e => e | e => e
  let arms := Suspend.chainArms dispatch
  let (ok, es) := match callE with
    | .call g es => (isS g, es)
    -- (each implementation the dispatch runs, with its own defaults)
    | _ => (!arms.isEmpty && arms.all (fun a => (Suspend.callsOf a).any (isS ·.1)), [])
  if !ok then eerr p "spawn{…} takes a call of a <suspends> function (#156)"
  -- (a spawn among them does not wait)
  let waits (x : Expr) := Suspend.countSusp isS (fun _ => false) false (· == mark.idx) x
  -- A dispatch arm includes the selected method call itself. Any other
  -- suspension belongs to its arguments, including inline defaults.
  if (pre ++ es).any (fun x => waits x > 0) || arms.any (fun x => waits x > 1) then
    eerr p "the arguments of a spawned call cannot suspend (#156)"
  let task := ctx.types.concurrencyName "task"
  let ty : Ty := .struct task [r.ty]
  let tagT := ctx.types.tagOf task
  let t ← fresh ty
  -- (its fields: the done flag `false`, the others empty options)
  let fieldVals := (ctx.types.fields task [r.ty]).map fun (_, ft, _) =>
    if ft == .logic then Expr.lit (.logic false) else Expr.lit .none
  let spawnE : Expr := .seq (.assign t (.heap (.new tagT) fieldVals))
    (.seq (.call mark.idx [.prim .mkArr [.seq callE (.lit .void), .seq (.local t) (.lit .void)]]) (.local t))
  modify fun st => { st with pendingSourceSuspends := sourceBefore }
  return ⟨pre.foldr Expr.seq spawnE, ty⟩

/-- `branch:` (#156): its body runs as a background task over the enclosing
    function's frame, at once up to its first wait, and is cancelled when
    the function exits. The lowering (`Suspend.lean`) turns the marker
    `$branchMark(array{body})` into an arm run as a task root. -/
partial def elabBranch (ctx : Ctx) (p : Pos) (body : SExpr) : EM R := do
  if !ctx.suspends then eerr p "branch suspends: it can only be used in a <suspends> function (#156)"
  if ctx.inDefer then eerr p "branch in a defer is not supported (#156)"
  if ctx.canFail then eerr p "branch cannot be in a failure context (a condition, a filter, or a <decides> call's arguments) (#156)"
  if ctx.inRepeat then eerr p "branch cannot be in a loop or for body (Book of Verse ch. 14): call a function that branches"
  let some mark := ctx.sig? "$branchMark" | eerr p "internal error: no branch helper"
  let armCtx := { ctx with defers := [], loopDefers := 0, inLoop := false, inArm := true, inBranch := true }
  let sourceBefore := (← get).pendingSourceSuspends
  let r ← elabE armCtx body none
  modify fun st => { st with pendingSourceSuspends := sourceBefore }
  noteBackgroundCaptures ctx (Suspend.slotsOf r.e)
  return ⟨.call mark.idx [.prim .mkArr [← discardValue r]], .void⟩

partial def elabDefersCore (ctx : Ctx) (ds : List (SExpr × List Local)) : EM Expr := do
  let mut acc : Expr := .lit .void
  for (d, locs) in ds.reverse do
    -- (with the locals where it was registered: their slots still hold them)
    -- (no failure context that takes a choice's values, #283)
    let dctx := { ctx with canFail := false, inRollback := ctx.inRollback || ctx.canFail,
                           inDefer := true, inLoop := false, defers := [], loopDefers := 0,
                           locals := locs, inTaking := false, liftWhy := "" }
    let r ← elabE dctx d none
    acc := .seq (← inferable r) acc
  return acc

/-- A call of an overloaded function or method (#74): the one overload
    (`ovs`, each with its signature `sigOf`, a method's without `Self`) the
    call's shape and arguments fit, then `call` it. -/
partial def resolveOverload (ctx : Ctx) (p : Pos) (name : String) (ovs : List String)
    (sigOf : String → Option Sig) (call : String → EM R) (args : List SExpr) : EM R := do
  -- an overloaded function (#74): the one overload whose parameters the
  -- arguments fit (each elaborated at the parameter's type, in a trial)
  -- the overloads the call's shape fits: as many positional arguments, and
  -- named ones the overload has, every one it needs given
  let isNamedArg : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
  let posArgs := args.filter (!isNamedArg ·)
  let namedArgs : List (String × SExpr) := args.filterMap fun
    | .decl _ n _ _ rhs => if n.startsWith "?" then some ((n.drop 1).toString, rhs) else none
    | _ => none
  let adapted ← ovs.mapM fun o => do
    let some s := sigOf o | return (o, args)
    return (s.name, packCallArgs p s args false)
  let posOf (s : Sig) : List SExpr := ((adapted.lookup s.name).getD args).filter (!isNamedArg ·)
  let fitsShape (s : Sig) : Bool :=
    (posOf s).length == s.params.length - s.named.length &&
    namedArgs.all (fun (g, _) => s.named.any (·.1 == g)) &&
    s.named.all fun (n, d) => d.isSome || namedArgs.any (·.1 == n)
  -- each argument expression with the type of its parameter in `s`
  let argTys (s : Sig) : List (SExpr × Ty) :=
    let npos := s.params.length - s.named.length
    ((posOf s).zip (s.params.take npos)) ++ namedArgs.filterMap fun (n, rhs) =>
      (s.named.findIdx? (·.1 == n)).map fun j => (rhs, (s.params.drop npos).getD j .void)
  let cands := ovs.filter fun o => ((sigOf o).map fitsShape).getD false
  -- each argument's type alone, once (none: it needs an expected type)
  let natTy (a : SExpr) : EM (Option Ty) := do
    -- Copied alternatives and polymorphic suffix trials revisit the same
    -- expression with different lexical types. Cache that context too;
    -- a stale natural type can otherwise select the wrong overload.
    let shape : String := match a with
      | .app _ (.ident _ f) as b => s!"app {f} {as.length} {b}"
      | .ident _ n => s!"id {n}"
      | .int _ v => s!"int {v}"
      | .member _ _ m => s!"mem {m}"
      | .construct _ n _ fs => s!"new {n} {fs.length}"
      | .tuple _ es => s!"tup {es.length}"
      | .arrayLit _ es => s!"arr {es.length}"
      | .bin _ o _ _ => s!"bin {o}"
      | _ => "_"
    let inputs := (ctx.capturesOf a).map fun l =>
      (l.name, l.ty, l.typeValue)
    let typing := reprStr (inputs, ctx.types.tvars, ctx.selfClass, ctx.selfMethod)
    let key := s!"{a.pos.line}:{a.pos.col}:{a.pos.file}:{shape}:{typing}"
    if let some r := (← get).natTys[key]? then return r
    let st ← get
    let r ← tryCatch (do return some (← elabE ctx a none).ty) (fun _ => pure none)
    let cache := (← get).natTys
    set { st with natTys := cache.insert key r, methodReceivers := (← get).methodReceivers }
    return r
  let coercible (t u : Ty) : EM Bool := do
    let st ← get
    let ok ← tryCatch (do discard <| coerce p ⟨.lit .void, t⟩ u; pure true) (fun _ => pure false)
    set { st with natTys := (← get).natTys, methodReceivers := (← get).methodReceivers }
    return ok
  let mut byNat : List String := []
  for o in cands do
    let some so := sigOf o | continue
    let mut ok := true
    if cands.length > 1 then
      -- (a generic one's patterns, by the matching that infers its type
      -- arguments: no whole-call trial at every level of a nested call)
      let mut σ : List (String × Ty) := []
      for (a, u) in argTys so do
        if let some t ← natTy a then
          if so.tparams.isEmpty then
            if !(← coercible t u) then ok := false
          else match u.matchArg ctx.types σ t with
            | some σ' => σ := σ'
            | none =>
              -- (against nothing bound: the pattern cannot take it; a
              -- conflict with earlier bindings only may be a subtype the
              -- call reconciles, so the candidate stays for the trial)
              if (u.matchArg ctx.types [] t).isNone && !(← coercible t u) then ok := false
    if ok then byNat := byNat ++ [o]
  let fits (o : String) : EM Bool := do
    let s := (sigOf o).get!
    let st ← get
    if !s.tparams.isEmpty then
      let ok ← tryCatch (do discard <| call o; pure true) (fun _ => pure false)
      set { st with natTys := (← get).natTys, methodReceivers := (← get).methodReceivers }
      return ok
    let ok ← tryCatch (do
        for (a, t) in argTys s do
          let r ← elabE ctx a (some t)
          discard <| coerce a.pos r t
        pure true) (fun _ => pure false)
    set { st with natTys := (← get).natTys, methodReceivers := (← get).methodReceivers }
    return ok
  -- the overloads the arguments' own types fit, then those the arguments
  -- elaborated at each one's parameter types fit
  let mut ok : List String := []
  if byNat.length == 1 then ok := byNat
  else
    -- (none: an argument's own type can differ from its type at a
    -- parameter, `false` is a logic and also fits `?t`)
    for o in (if byNat.isEmpty then cands else byNat) do
      if ← fits o then ok := ok ++ [o]
  let call' (o : String) : EM R :=
    tryCatch (call o) fun msg => throw (msg.replace o name)
  match ok, cands with
  | [o], _ => call' o
  | [], [o] => call' o   -- its error
  | [], [] =>
    let nm := if namedArgs.isEmpty then "" else s!" and {", ".intercalate (namedArgs.map fun (n, _) => s!"?{n}")}"
    let shown := ovs.filterMap fun o => (sigOf o).map fun so =>
      let npos := so.params.length - so.named.length
      "(" ++ ", ".intercalate ((so.params.take npos).map Ty.show ++
        (so.named.zip (so.params.drop npos)).map fun ((n, d), t) =>
          s!"?{n}:{t.show}" ++ (if d.isSome then " = …" else "")) ++ ")"
    eerr p s!"no overload of {name} fits a call with {posArgs.length} positional argument(s){nm}; its overloads take {" and ".intercalate shown}"
  | [], _ =>
    let st ← get
    let tys ← posArgs.mapM fun a => do return (← elabE ctx a none).ty.show
    let ntys ← namedArgs.mapM fun (n, a) => do return s!"?{n}:{(← elabE ctx a none).ty.show}"
    let tys := tys ++ ntys
    set st
    eerr p s!"no overload of {name} takes ({", ".intercalate tys})"
  | _ :: _ :: _, _ =>
    let shown := ok.map fun o => s!"({", ".intercalate (((sigOf o).map (·.params)).getD [] |>.map Ty.show)})"
    eerr p s!"this call of {name} fits more than one overload: {" and ".intercalate shown}"

/-- Clauses (a condition's, a filter's, the code before a value), threading
    the scope: their names stay in it, and their value, the last one's,
    nothing takes (`inferable`). -/
partial def elabSeq (ctx : Ctx) (ss : List SExpr) (exp : Option Ty) : EM (R × Ctx) := do
  let (r, c) ← elabSeqIn false ctx ss exp
  return (⟨← inferable r, r.ty⟩, c)

/-- `elabSeq`, and, for a sequence whose names end with it (`closed`: a
    block) in a failure context, a cast that refines type arguments there
    takes the rest of the sequence as its branch (#243): `pre; D := T[X];
    rest` is `pre; if (D := T[X]) then {rest} else fail`, the rest typed
    under the refinement, and its failure, or the cast's, the sequence's, so
    that what `pre` did is undone with it. A bare `T[X]` is so too, its
    value named for the branch. -/
partial def elabSeqIn (closed : Bool) (ctx : Ctx) (ss : List SExpr) (exp : Option Ty) : EM (R × Ctx) := do
  match ss with
  | [] => return (⟨.lit .void, .void⟩, ctx)
  | .app p (.ident _ "$defer") [body] false :: rest =>
    -- `defer: D` then the rest of the scope (Book of Verse ch. 7): the rest,
    -- with D pending for its returns and breaks, then D, then the rest's value
    if let .block _ [] := body then eerr p "a defer: block cannot be empty"
    let (r2, ctx2) ← elabSeqIn closed (ctx.withDefer body) rest exp
    let d ← elabDefers ctx [(body, ctx.locals)]
    let ctx2 := { ctx2 with defers := ctx.defers, loopDefers := ctx.loopDefers }
    match r2.ty with
    | .never => return (r2, ctx2)
    | .void => return (⟨.seq r2.e (.seq d (.lit .void)), .void⟩, ctx2)
    | ty =>
      let t ← fresh ty
      return (⟨.seq (.assign t r2.e) (.seq d (.local t)), ty⟩, ctx2)
  | s :: rest =>
    if closed && ctx.canFail then
      if let some (p, d, T, x) := Refine.castClause? s then
        let branch := if rest.isEmpty then .ident p d else .block p rest
        if let some r ← elabRefinedIf ctx p p d T x branch (some (Refine.noValue p)) exp (made := true) then
          return (r, ctx)
    -- (a cast inside the statement that only a clause may be, refused
    -- there: lifted out to be a statement of its own, `liftCastClause`)
    let stmtExp := if rest.isEmpty then exp else none
    let inner := if closed && ctx.canFail then Refine.castsIn ctx.types.classes.contains s else []
    let (r, ctx') ← if inner.isEmpty then elabStmt ctx s stmtExp else
      match ← tryCatch (Except.ok <$> elabStmt ctx s stmtExp) (fun err => pure (Except.error err)) with
      | .ok rc => pure rc
      | .error err =>
        match Refine.castRefusal? err with
        | some r =>
          if inner.contains r.pos then return ← elabSeqIn closed ctx (liftCastClause ctx [] r.pos s ++ rest) exp
          throw err
        | none => throw err
    if rest.isEmpty then return (r, ctx')
    let e ← inferable r
    let (r2, ctx'') ← elabSeqIn closed ctx' rest exp
    return (⟨.seq e r2.e, r2.ty⟩, ctx'')

partial def elabArgs (ctx : Ctx) (p : Pos) (args : List SExpr) (tys : List Ty) : EM (List Expr) := do
  if args.length != tys.length then
    eerr p s!"expected {tys.length} argument(s), found {args.length}"
  (args.zip tys).mapM fun (a, t) => do coerce a.pos (← elabE ctx a (some t)) t

partial def elabInts (ctx : Ctx) (p : Pos) (args : List SExpr) : EM (List Expr) :=
  elabArgs ctx p args (args.map fun _ => .int)

/-- A call. One tuple argument that a call cannot take as it is is expanded
    into several (Book of Verse ch. 3, #140): of a method, an overloaded or a
    generic function as of any other (`elabAppBase` does plain calls). -/
partial def elabApp (ctx : Ctx) (p : Pos) (f : SExpr) (args : List SExpr) (bracket : Bool)
    (exp : Option Ty) : EM R := do
  let isNamed : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
  let positional := args.filter (!isNamed ·)
  let namedArgs := args.filter isNamed
  -- A method function keeps its receiver as the first argument.
  -- Inlining already spreads a following tuple, but kept/scalar/array calls
  -- reach this boundary directly. Instantiate from the actual receiver;
  -- callee type names have no meaning in the caller's lexical type scope.
  if let (.ident _ g, [receiver, tupleArg]) := (f, positional) then
    if let some s := ctx.sig? g then
      let npos := s.params.length - s.named.length
      if s.hasReceiver && npos ≥ 3 then
        let r ← elabE ctx receiver none
        let some σ := s.params[0]!.matchArg ctx.types [] r.ty
          | eerr receiver.pos s!"expected {s.params[0]!.show}, found {r.ty.show} (the receiver of {Choice.shownFnName g})"
        let pattern := Ty.tup (s.params.drop 1 |>.take (npos - 1))
        let known := pattern.params.all fun n => (σ.lookup n).isSome
        let rv ← fresh r.ty
        let rn := s!"$methodReceiver{rv}"
        let c := { ctx with locals := { name := rn, slot := rv, ty := r.ty, mutable := false } :: ctx.locals }
        if !known then
          if let .tuple _ fields := tupleArg then
            let out ← elabAppBase c p f (.ident p rn :: fields ++ namedArgs) bracket exp
            return ⟨.seq (.assign rv r.e) out.e, out.ty⟩
          let tuple ← elabE ctx tupleArg none
          let .tup ts := tuple.ty
            | eerr tupleArg.pos s!"expected tuple argument of {Choice.shownFnName g}, found {tuple.ty.show}"
          let tv ← fresh tuple.ty
          let tn := s!"$methodTuple{tv}"
          let c := { c with locals := { name := tn, slot := tv, ty := tuple.ty, mutable := false } :: c.locals }
          let parts := ts.zipIdx.map fun (_, i) =>
            SExpr.app tupleArg.pos (.ident tupleArg.pos tn) [.int tupleArg.pos (i : Int)] false
          let out ← elabAppBase c p f (.ident p rn :: parts ++ namedArgs) bracket exp
          return ⟨.seq (.assign rv r.e) (.seq (.assign tv tuple.e) out.e), out.ty⟩
        let ty := pattern.subst σ
        let tuple ← coerce tupleArg.pos (← elabE ctx tupleArg (some ty)) ty
        let tv ← fresh ty
        let tn := s!"$methodTuple{tv}"
        let c := { c with locals := { name := tn, slot := tv, ty, mutable := false } :: c.locals }
        let parts := (List.range (npos - 1)).map fun (i : Nat) =>
          SExpr.app tupleArg.pos (.ident tupleArg.pos tn) [.int tupleArg.pos (i : Int)] false
        let out ← elabAppBase c p f (.ident p rn :: parts ++ namedArgs) bracket exp
        return ⟨.seq (.assign rv r.e) (.seq (.assign tv tuple) out.e), out.ty⟩
  -- A literal tuple's fields are the call's positional arguments. Let the
  -- ordinary binder infer generic instances before contextual empty fields,
  -- including in the retained body used to check a multi-value function.
  if let (.ident _ g, [.tuple _ fields]) := (f, positional) then
    if let some s := ctx.sig? g then
      let selfMember := ctx.selfClass.any fun c => ctx.hasMethod c g ||
        ((ctx.types.methodOverloads.lookup g).map (·.any (ctx.hasMethod c ·))).getD false ||
        ((ctx.types.fields c).any (·.1 == g) && !builtins.contains g && !softBuiltins.contains g)
      if (ctx.lookup g).isNone && !selfMember && s.params.length - s.named.length > 1 then
        return ← elabAppBase ctx p f (fields ++ namedArgs) bracket exp
  match positional with
  | [a] =>
    -- (nested retries are bounded: each level elaborates its argument again)
    if ctx.retries ≥ 8 then return ← elabAppBase ctx p f args bracket exp
    let saved ← get
    -- (the state is restored between attempts, but not the overload cache)
    let restore : EM Unit := do set { saved with natTys := (← get).natTys, methodReceivers := (← get).methodReceivers }
    tryCatch (elabAppBase ctx p f args bracket exp) fun err => do
      -- A one-argument candidate may fail its type, effects or call syntax
      -- before discovering a tuple for a different flattened overload.
      -- Keep the existing shape retries. Additional errors must originate
      -- at this call, or report a tuple mismatch at its argument: retrying
      -- arbitrary nested producer errors causes repeated failed elaboration.
      -- The argument must independently elaborate to a tuple and the expanded
      -- call must pass ordinary checks; otherwise retain the original error.
      let shapeErr := ["argument(s)", "overload", "expected tuple"].any
        fun k => (err.splitOn k).length > 1
      let callErr := err.startsWith s!"{p.show}:"
      let tupleErr := err.startsWith s!"{a.pos.show}:" &&
        (err.splitOn ", found tuple(").length > 1
      if !(shapeErr || callErr || tupleErr) then throw err
      restore
      let c2 := { ctx with retries := ctx.retries + 1 }
      let fnTy : Ty → Bool := fun | .struct n _ => (FnValues.parseName n).isSome | _ => false
      -- a method's receiver is evaluated first, then the tuple
      let (pre, c2, f') ← match f with
        | .member mp obj m =>
          if (match obj with | .ident _ "(super:)" => true | _ => false) then pure ([], c2, f) else
          match ← tryCatch (some <$> elabE c2 obj none) (fun _ => pure none) with
          | some ro =>
            let to ← fresh ro.ty
            let nm := s!"$receiver{to}"
            pure ([Expr.assign to ro.e],
              { c2 with locals := { name := nm, slot := to, ty := ro.ty, mutable := false } :: c2.locals },
              SExpr.member mp (.ident mp nm) m)
          | none => pure ([], c2, f)
        | _ => pure ([], c2, f)
      -- Callable values are read before their argument tuple, including a
      -- mutable local/field or a returned value. Saving only a field's object
      -- would let the tuple producer replace the function before it is read.
      let valueCallee ← match f' with
        | .ident _ n => pure (((c2.lookup n).map (fun l => fnTy l.ty)).getD false ||
            (c2.sig? n).any (fun s => s.isConst && fnTy s.ret))
        | .member _ obj m =>
          match (elabE { c2 with typeOnly := true } obj none).run (← get) with
          | .ok (⟨_, .struct c as⟩, _) =>
            pure ((c2.types.fields c as).any fun (n, ft, _) => n == m && fnTy ft)
          | _ => pure false
        | _ =>
          match (elabE { c2 with typeOnly := true } f' none).run (← get) with
          | .ok (r, _) => pure (fnTy r.ty)
          | _ => pure false
      let (pre, c2, f') ← if valueCallee then do
          let value ← elabE c2 f' none
          let slot ← fresh value.ty
          let name := s!"$tupleCallee{slot}"
          pure (pre ++ [Expr.assign slot value.e],
            { c2 with locals := { name, slot, ty := value.ty, mutable := false } :: c2.locals },
            SExpr.ident f'.pos name)
        else pure (pre, c2, f')
      match ← tryCatch (some <$> elabE c2 a none) (fun _ => pure none) with
      | some ⟨e, ty⟩ =>
        let some ts := (match ty with | .tup ts => some ts | .void => some [] | _ => none)
          | restore; throw err
        if ts.length < 2 then
          -- Unit and singleton tuple flattening belongs to functions.
          -- Keep casts and collection indexing at their ordinary types.
          let functionHead ← match f' with
            | .ident _ n =>
              if let some l := c2.lookup n then pure (fnTy l.ty) else
              pure ((c2.sig? n).any (fun s => !s.isConst || fnTy s.ret) ||
                (c2.types.overloads.lookup n).isSome || (c2.sig? s!"{n}$init").isSome ||
                (c2.types.overloads.lookup s!"{n}$init").isSome || c2.selfClass.any (c2.hasMethod · n))
            | .member _ (.ident _ "(super:)") _ => pure true
            | .member _ obj m =>
              match (elabE { c2 with typeOnly := true } obj none).run (← get) with
              | .ok (⟨_, .struct c as⟩, _) =>
                match (c2.types.fields c as).find? (·.1 == m) with
                | some (_, ft, _) => pure (fnTy ft)
                | none => pure (c2.types.classes.contains c)
              | _ => pure false
            | _ =>
              match (elabE { c2 with typeOnly := true } f' none).run (← get) with
              | .ok (r, _) => pure (fnTy r.ty)
              | _ => pure false
          if !functionHead then restore; throw err
        let tt ← fresh ty
        let nm := s!"$tuple{tt}"
        let c3 := { c2 with locals := { name := nm, slot := tt, ty, mutable := false } :: c2.locals }
        let parts := (List.range ts.length).map fun (i : Nat) => SExpr.app a.pos (.ident a.pos nm) [.int a.pos (i : Int)] false
        match ← tryCatch (some <$> elabAppBase c3 p f' (parts ++ namedArgs) bracket exp) (fun _ => pure none) with
        | some r => return ⟨(pre ++ [Expr.assign tt e]).foldr Expr.seq r.e, r.ty⟩
        | none => restore; throw err
      | _ => restore; throw err
  | _ => elabAppBase ctx p f args bracket exp

partial def elabAppBase (ctx : Ctx) (p : Pos) (f : SExpr) (args : List SExpr) (bracket : Bool)
    (exp : Option Ty) : EM R :=
  elabAppBaseWith elabE withDeferMark elabSpawn resolveOverload elabArgs elabInts elabApp elabCast elabGenericCall elabMethod elabIndexLike elabSpawnDispatch elabDefaultDispatch (@elabMember) ctx p f args bracket exp

/-- `T[X]`: `X` as a value of class or interface `T`, failing unless its class
    is below `T`; `T(X)`: an upcast, which cannot fail (Book of Verse ch. 10). -/
partial def elabCast (ctx : Ctx) (p : Pos) (T : String) (args : List SExpr) (bracket : Bool) : EM R := do
  let env := ctx.types
  let [a] := args | eerr p s!"a cast {T}[X] takes one value"
  let r ← elabE ctx a none
  let (S, sargs) ← match r.ty with
    | .struct S sargs => if env.classes.contains S then pure (S, sargs) else eerr p s!"cannot cast {withArticle S} to {T}"
    | t => eerr p s!"cannot cast {withArticle t.show} to {T}"
  -- (#351) from a reference through views, a cast to a class or interface
  -- with Verse Core type arguments takes them from a dispatch: as a clause
  -- of a failure context, whose rest is a function of its own
  if bracket && env.viewed.contains S && !(env.coreArgs T (((env.sparams.lookup T).getD []).map fun (v, k) => Ty.param v k)).isEmpty then
    let what := s!"a cast of {withArticle r.ty.show}, an interface referred to through views, to {T}"
    if env.isSub S T then
      eerr p s!"{what}, which is above {S}, cannot fail: use {T}(…), an upcast (#351)"
    -- (no class below both whose view and pins can give the object's type
    -- arguments: it would always fail, as main says of a positional one)
    if !viewsMayBe env S sargs T then
      eerr p s!"{withArticle r.ty.show} is never {withArticle T}: no class below both gives {S} those type arguments, so {T}[…] would always fail"
    -- (one a clause does not take either; to a type beside it, or to an
    -- interface whose type arguments it opens, a clause takes it as a cast
    -- to each class below both, #53)
    if (refiningCast? env T r.ty).isNone then
      eerr p s!"{what} would leave {T}'s type arguments unknown: they are not {S}'s (#351, #53)"
    let theirs := if (env.sparams.lookup T).isNone then s!"the type arguments {T} fixes" else s!"{T}'s type arguments"
    let opens := (refiningCast? env T r.ty).any fun (_, _, _, _, _, opened) => !opened.isEmpty
    throw (Refine.castRefusal { pos := p, opens } s!"{what} works {Refine.castRefusalNote}, D := {T}[X], whose rest then has {theirs} (#351)")
  -- a parametric class's type arguments are those of the value (#39), in the
  -- same hierarchy
  let parametric := (env.sparams.lookup T).isSome || !(env.coreArgs T []).isEmpty
  if (env.concreteBelow S).all (fun d => !env.isSub d T) then
    eerr p s!"no class is below both {r.ty.show} and {T}, so {T}[…] would always fail"
  -- (#351, #53: to a type beside it, whose type arguments the classes and
  -- interfaces above both relate to the object's, and open otherwise: as a
  -- clause, a cast to each class below both)
  if parametric && !(env.isSub S T || env.isSub T S) then
    let some (_, _, _, _, _, opened) := refiningCast? env T r.ty
      | eerr p s!"cannot cast {withArticle S} to {T}: {T}'s type arguments would be unknown (they are not {S}'s)"
    throw (Refine.castRefusal { pos := p, opens := !opened.isEmpty } s!"a cast of {withArticle r.ty.show} to {T}, which is neither above nor below {S}, works {Refine.castRefusalNote}, D := {T}[X], whose rest then has {T}'s type arguments (#351, #53)")
  let targs := if env.isSub S T then env.upArgs S sargs T else env.argsBelow S sargs T
  if parametric && (env.coreArgs T targs).length > (env.coreArgs S sargs).length then
    let unknown := s!"cannot cast {withArticle r.ty.show} to {T}: {T} has type parameters that {S} does not have, which would be unknown here"
    -- (an interface has no hidden fields to read opened ones from, #53)
    if (env.info T).isIface && (refiningCast? env T r.ty).isNone then eerr p s!"{unknown} (#53, #250)"
    throw (Refine.castRefusal { pos := p, opens := true } s!"{unknown}: a cast opens them {Refine.castRefusalNote}, D := {T}[X], whose rest then has them (#250)")
  if bracket then
    match env.refineComparable? [] (env.comparableArgs T targs) with
    | none => eerr p s!"{withArticle r.ty.show} is never {withArticle T}: its type arguments do not satisfy {T}'s comparable bounds"
    | some μ =>
      if !μ.isEmpty then
        throw (Refine.castRefusal { pos := p, opens := false } s!"a cast to {T} strengthens comparable bounds, which works {Refine.castRefusalNote}, D := {T}[X], whose rest then has them (#209)")
  let tty : Ty := .struct T targs
  if !bracket then
    if !env.isSub S T then
      eerr p s!"{T}(…) converts to a supertype, and {S} is not below {T}: use {T}[…] to cast down"
    return ⟨← coerce p r tty, tty⟩
  let below := env.concreteBelow S
  let common := below.filter (env.isSub · T)
  if common.isEmpty then
    eerr p s!"no class is below both {r.ty.show} and {T}, so {T}[…] would always fail"
  if parametric && env.coreArgs T targs != env.coreArgs S sargs then
    if (Ty.unifyEqs (fun _ _ => none) [] ((env.coreArgs S sargs).zip (env.coreArgs T targs))).isSome then
      throw (Refine.castRefusal { pos := p, opens := false } s!"cannot cast {withArticle r.ty.show} to {(Ty.struct T targs).show} here: their type arguments agree only under a refinement, which a cast gives {Refine.castRefusalNote}, D := {T}[X], whose rest is then typed under it (#209, #243)")
    -- (in a class's copy of an interface's default, at type arguments the
    -- class fixes, it fails, as the interface's own default's would, #53)
    if !ctx.liftTag.isEmpty then return ⟨.prim .fail [], tty⟩
    eerr p s!"{withArticle r.ty.show} is never {withArticle T}: their type arguments differ, so {T}[…] would always fail"
  -- a reference: a test of its object's class (#34)
  if env.isRefClass S then return ⟨.heap (.isTag (common.map env.tagOf)) [r.e], tty⟩
  let x ← fresh r.ty
  let mut acc : Expr := .prim .fail []
  for d in common.reverse do
    let j := (below.idxOf? d).getD 0
    let td ← fresh (classRepTy env d)
    acc := .ite (.assign td (.prim .query [.prim (.tupGet j) [.local x]])) (classWrap env T d (.local td)) acc
  let y ← fresh (.struct T [])
  return ⟨.seq (.assign x r.e) (.assign y acc), .struct T []⟩

/-- `elabRefinedIfWith`, given this block's functions (#325). -/
partial def elabRefinedIf (ctx : Ctx) (p _dp : Pos) (D T : String) (x : SExpr) (body0 : SExpr)
    (elseE : Option SExpr) (exp : Option Ty) (made : Bool := false) : EM (Option R) :=
  elabRefinedIfWith elabApp elabE withDeferMark ctx p _dp D T x body0 elseE exp made

/-- `refinedIfTypeWith`, given this block's functions. -/
partial def refinedIfType (ctx : Ctx) (p : Pos) (D T : String) (x body ee : SExpr) :
    EM (Option (Ty × Bool)) :=
  refinedIfTypeWith elabE ctx p D T x body ee

/-- `elabGenericCallWith`, given this block's functions (#325). -/
partial def elabGenericCall (ctx : Ctx) (p : Pos) (s : Sig) (args : List SExpr) (exp : Option Ty) :
    EM R :=
  elabGenericCallWith elabE ctx p s args exp

/-- The failable array methods of the Book of Verse (§9.1):
    `A.Slice[i, j]`, `A.Slice[i]`, `A.Find[x]`, `A.RemoveElement[i]`,
    `A.ReplaceElement[i, x]`, `A.Insert[i, B]`, `A.Last[]`, `A.Last[n]`. Each fails when an index is
    out of range (or, for `Find`, when there is no such element). -/
partial def elabMethod (ctx : Ctx) (p : Pos) (r : R) (m : String) (args : List SExpr) (bracket : Bool) :
    EM R := do
  let .arr t := r.ty | eerr p s!"{r.ty.show} has no method '{m}'"
  -- (the methods that cannot fail take parentheses, #150)
  let total := ["RemoveAllElements", "ReplaceAllElements", "ReplaceAll"].contains m
  if total && bracket then eerr p s!"{m} cannot fail: call it with A.{m}(…)"
  if !total && !bracket then eerr p s!"{m} can fail: call it with A.{m}[…]"
  let ta ← fresh r.ty
  let len := Expr.prim .len [.local ta]
  let int (i : Int) : Expr := .lit (.int i)
  -- the elements of A at indices lo, …, hi - 1 (lo ≤ hi known)
  let slice (lo hi : Expr) : EM Expr := do
    let ti ← fresh .int
    let tx ← fresh t
    return .forE ti (.prim .range [lo, p2 .sub hi (int 1)]) (.assign tx (p2 .index (.local ta) (.local ti)))
      (.local tx)
  let start := Expr.assign ta r.e
  match m, args with
  | "Slice", [a, b] =>
    let es ← elabInts ctx p [a, b]
    let tlo ← fresh .int
    let thi ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tlo)) (.seq (p2 .le (.local tlo) (.local thi))
      (p2 .le (.local thi) len))
    return ⟨.seq start (.seq (.assign tlo es[0]!) (.seq (.assign thi es[1]!) (.seq chk
      (← slice (.local tlo) (.local thi))))), r.ty⟩
  | "Slice", [a] =>
    let es ← elabInts ctx p [a]
    let tlo ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tlo)) (p2 .le (.local tlo) len)
    return ⟨.seq start (.seq (.assign tlo es[0]!) (.seq chk (← slice (.local tlo) len))), r.ty⟩
  | "Find", [x] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t "the element type of Find")
    let rx ← elabE ctx x (some t)
    let tx ← fresh t
    let ti ← fresh .int
    let found := Expr.forE ti (.prim .range [int 0, p2 .sub len (int 1)])
      (p2 .eq (p2 .index (.local ta) (.local ti)) (.local tx)) (.local ti)
    return ⟨.seq start (.seq (.assign tx (← coerce p rx t)) (p2 .index found (int 0))), .int⟩
  -- `A.Last[]` is the last element, `A.Last[N]` the one N before it (Book of
  -- Verse ch. 3): failing when there is none
  | "Last", [] => return ⟨.seq start (p2 .index (.local ta) (p2 .sub len (int 1))), t⟩
  | "Last", [n] =>
    let es ← elabInts ctx p [n]
    return ⟨.seq start (p2 .index (.local ta) (p2 .sub (p2 .sub len (int 1)) es[0]!)), t⟩
  | "RemoveElement", [i] =>
    let es ← elabInts ctx p [i]
    let tk ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tk)) (p2 .lt (.local tk) len)
    return ⟨.seq start (.seq (.assign tk es[0]!) (.seq chk
      (p2 .concat (← slice (int 0) (.local tk)) (← slice (p2 .add (.local tk) (int 1)) len)))), r.ty⟩
  | "ReplaceElement", [i, x] =>
    let es ← elabInts ctx p [i]
    let rx ← elabE ctx x (some t)
    return ⟨.seq start (.prim .arrSet [.local ta, es[0]!, ← coerce p rx t]), r.ty⟩
  | "Insert", [i, b] =>
    let es ← elabInts ctx p [i]
    let rb ← elabE ctx b (some r.ty)
    let tk ← fresh .int
    let tb ← fresh r.ty
    let chk := Expr.seq (p2 .le (int 0) (.local tk)) (p2 .le (.local tk) len)
    return ⟨.seq start (.seq (.assign tk es[0]!) (.seq (.assign tb (← coerce p rb r.ty)) (.seq chk
      (p2 .concat (p2 .concat (← slice (int 0) (.local tk)) (.local tb)) (← slice (.local tk) len))))), r.ty⟩
  -- (#150) the first occurrence of `x`, removed or replaced: failing when
  -- there is none
  | "RemoveFirstElement", [x] | "ReplaceFirstElement", [x, _] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t s!"the element type of {m}")
    let rx ← elabE ctx x (some t)
    let tx ← fresh t
    let ti ← fresh .int
    let found := Expr.forE ti (.prim .range [int 0, p2 .sub len (int 1)])
      (p2 .eq (p2 .index (.local ta) (.local ti)) (.local tx)) (.local ti)
    let tk ← fresh .int
    let first := Expr.seq (.assign tx (← coerce p rx t)) (.assign tk (p2 .index found (int 0)))
    match m, args with
    | "ReplaceFirstElement", [_, y] =>
      let ry ← elabE ctx y (some t)
      return ⟨.seq start (.seq first (.prim .arrSet [.local ta, .local tk, ← coerce p ry t])), r.ty⟩
    | _, _ =>
      return ⟨.seq start (.seq first
        (p2 .concat (← slice (int 0) (.local tk)) (← slice (p2 .add (.local tk) (int 1)) len))), r.ty⟩
  -- `A.Remove[i, j]`: without the elements i…j-1 (0 ≤ i ≤ j ≤ the length)
  | "Remove", [a, b] =>
    let es ← elabInts ctx p [a, b]
    let tlo ← fresh .int
    let thi ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tlo)) (.seq (p2 .le (.local tlo) (.local thi))
      (p2 .le (.local thi) len))
    return ⟨.seq start (.seq (.assign tlo es[0]!) (.seq (.assign thi es[1]!) (.seq chk
      (p2 .concat (← slice (int 0) (.local tlo)) (← slice (.local thi) len))))), r.ty⟩
  -- every occurrence of `x`, removed or replaced: never failing
  | "RemoveAllElements", [x] | "ReplaceAllElements", [x, _] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t s!"the element type of {m}")
    let rx ← elabE ctx x (some t)
    let tx ← fresh t
    let te ← fresh t
    let setX := Expr.assign tx (← coerce p rx t)
    match m, args with
    | "ReplaceAllElements", [_, y] =>
      let ry ← elabE ctx y (some t)
      let ty ← fresh t
      return ⟨.seq start (.seq setX (.seq (.assign ty (← coerce p ry t))
        (.forE te (.local ta) (.lit .void)
          (.ite (p2 .eq (.local te) (.local tx)) (.local ty) (.local te))))), r.ty⟩
    | _, _ =>
      return ⟨.seq start (.seq setX (.forE te (.local ta) (p2 .ne (.local te) (.local tx)) (.local te))), r.ty⟩
  -- `A.ReplaceAll(Pattern, Replacement)`: a helper written in Verse
  | "ReplaceAll", [pat, rep] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t "the element type of ReplaceAll")
    let nm := s!"$receiver{ta}"
    let c2 := { ctx with locals := { name := nm, slot := ta, ty := r.ty, mutable := false } :: ctx.locals }
    let rc ← elabApp c2 p (.ident p "$replaceAll") [.ident p nm, pat, rep] false (some r.ty)
    return ⟨.seq start rc.e, r.ty⟩
  | _, _ => eerr p s!"unknown array method '{m}' with {args.length} argument(s) (openverse supports Slice, Find, RemoveFirstElement, RemoveElement, Remove, RemoveAllElements, ReplaceFirstElement, ReplaceElement, ReplaceAllElements, ReplaceAll, Insert, Last)"

/-- `A[i]` on an array (failable) or `T(k)` on a tuple. -/
partial def elabIndexLike (ctx : Ctx) (p : Pos) (r : R) (args : List SExpr) (bracket : Bool) : EM R := do
  let containers : Ty → Bool := fun
    | .arr _ | .map .. => bracket
    | .tup _ => !bracket
    | _ => false
  let container ← match ctx.containerView p r.ty containers "index" with
    | .ok view => pure view
    | .error message => throw message
  if container.isSome then
    let callable ← match ctx.callableView p r.ty with
      | .ok view => pure view
      | .error message => throw message
    if callable.isSome then eerr p s!"ambiguous callable/index bound of {r.ty.show}"
  let r ← elabContainerReceiverWith elabE ctx p r containers "index"
  let r ← elabCallableReceiver ctx p r
  -- a call of a function value (#210): of its shape's method
  if let .struct n ts := r.ty then
    if let some (_, effs) := FnValues.parseName n then
      if effs.contains "decides" && !bracket then
        eerr p s!"a value of type {r.ty.show} can fail: call it with […]"
      if !effs.contains "decides" && bracket then
        eerr p s!"a value of type {r.ty.show} cannot fail: call it with (…)"
      if effs.contains "suspends" && !ctx.suspends then
        eerr p s!"a value of type {r.ty.show} suspends: it can only be called in a <suspends> function (#156)"
      -- (one tuple argument flattens into several parameters)
      let k := (FnValues.parseName n).elim 0 (·.1)
      let shape : Sig := { idx := 0, name := n, params := ts.take k, ret := .void, decides := false, isConst := false }
      let args := packCallArgs p shape args false
      if args.length != k && !(args.length == 1 && k > 1) then
        eerr p s!"a value of type {r.ty.show} takes {k} argument(s), found {args.length}"
      let t ← fresh r.ty
      if !ctx.typeOnly then
        modify fun st => { st with metadataUses := t :: st.metadataUses }
      let nm := s!"$fnval{t}"
      let ctx' := { ctx with locals := { name := nm, slot := t, ty := r.ty, mutable := false } :: ctx.locals }
      let rc ← elabApp ctx' p (.member p (.ident p nm) (FnValues.callOf n)) args bracket none
      -- A type-only operation dictionary may discard this call's Expr
      -- while retaining its result type. Keep the source wait visible to
      -- the enclosing continuation; merely reading a callable stays immediate.
      if ctx.typeOnly && effs.contains "suspends" then
        modify fun st => { st with
          pendingSuspendingCasts := st.pendingSuspendingCasts + 1,
          pendingWaitingCasts := st.pendingWaitingCasts + 1,
          pendingSourceSuspends := st.pendingSourceSuspends + 1 }
      return ⟨.seq (.assign t r.e) rc.e, rc.ty⟩
  match r.ty, args, bracket with
  | .arr t, [i], true =>
    let ri := widenR ctx.types (← elabE ctx i (some .int))
    if ri.ty != .int then eerr p s!"an array index must be an int, found {ri.ty.show}"
    return ⟨p2 .index (← inferable r) ri.e, t⟩
  | .map kt vt, [k], true =>
    let tm ← fresh r.ty
    let rk ← elabE ctx k (some kt)
    let tk ← fresh kt
    let tp ← fresh (.tup [kt, vt])
    return ⟨.seq (.assign tm r.e) (.seq (.assign tk (← coerce p rk kt)) (mapLookup tm tk tp)), vt⟩
  | .tup ts, [.int _ k], false =>
    if k < 0 || k.toNat ≥ ts.length then eerr p s!"tuple index {k} out of range"
    return ⟨.prim (.tupGet k.toNat) [← inferable r], ts[k.toNat]!⟩
  | t, _, _ => eerr p s!"cannot call or index a value of type {t.show}"

/-- Two types with an int in one where the other has a rational, at the
    same place inside them (#116). -/
partial def ratMismatch : Ty → Ty → Bool
  | .int, .rational | .rational, .int => true
  | .arr a, .arr b | .opt a, .opt b => ratMismatch a b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).any fun (a, b) => ratMismatch a b
  | .tup as, .arr b | .arr b, .tup as => as.any (ratMismatch · b)
  | .map k v, .map k' v' => ratMismatch k k' || ratMismatch v v'
  | .struct a as, .struct b bs => a == b && as.length == bs.length && (as.zip bs).any fun (x, y) => ratMismatch x y
  | _, _ => false

/-- Two different scalar types at the same place inside two types (#127):
    `1 = 1.0` or `array{1} = array{'a'}` would compare values Verse Core
    holds differently, always unequal. -/
partial def scalarMismatch : Ty → Ty → Bool
  | .arr a, .arr b | .opt a, .opt b => scalarMismatch a b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).any fun (a, b) => scalarMismatch a b
  | .tup as, .arr b | .arr b, .tup as => as.any (scalarMismatch · b)
  | .map k v, .map k' v' => scalarMismatch k k' || scalarMismatch v v'
  | .struct a as, .struct b bs => a == b && as.length == bs.length && (as.zip bs).any fun (x, y) => scalarMismatch x y
  | a, b =>
    let scalar : Ty → Bool := fun
      | .int | .logic | .char | .char32 | .rational | .float | .enum _ => true
      | _ => false
    scalar a && scalar b && !(a == b)

/-- A call of a rational helper (#116), `$ratMake` or `$ratLt`. -/
partial def ratCall (ctx : Ctx) (p : Pos) (f : String) (args : List Expr) : EM Expr := do
  let some s := ctx.sig? f | eerr p "internal error: the rational helpers are missing"
  return .call s.idx args

/-- The test of `x op y`, where one operand is a rational and the other an
    int or a rational (#116): it fails when the comparison does not hold.
    Rationals are in lowest terms, so `=` and `<>` are the tuples'; an
    ordering is `$ratLt`'s. -/
partial def ratTest (ctx : Ctx) (p : Pos) (op : String) (x y : R) : EM Expr := do
  let asRat (r : R) : EM Expr := match r.ty with
    | .rational => pure r.e
    | .int => pure (.prim .mkTup [r.e, .lit (.int 1)])
    | t => eerr p s!"'{op}' compares a rational with an int or a rational, not with {t.show}"
  let xa ← asRat x
  let ya ← asRat y
  match op with
  | "=" => return p2 .eq xa ya
  | "<>" => return p2 .ne xa ya
  | "<" => ratCall ctx p "$ratLt" [xa, ya]
  | ">" => ratCall ctx p "$ratLt" [ya, xa]
  | "<=" => return Expr.notE (← ratCall ctx p "$ratLt" [ya, xa])
  | _ => return Expr.notE (← ratCall ctx p "$ratLt" [xa, ya])

partial def elabCmp (ctx : Ctx) (p : Pos) (a : SExpr) (rest : List (String × SExpr)) : EM R := do
  let opOf : String → Prim
    | "=" => .eq | "<>" => .ne | "<" => .lt | "<=" => .le | ">" => .gt | _ => .ge
  -- (the orderings of floats are IEEE's, #127: false on NaN)
  let ordOf (op : String) (t : Ty) : Prim :=
    if t == .float then
      match op with
      | "<" => .flt | "<=" => .fle | ">" => .fgt | ">=" => .fge | _ => opOf op
    else opOf op
  let checkTys (op : String) (ta tb : Ty) : EM Unit := do
    if op == "=" || op == "<>" then
      if !isComparable ctx.types ta || !isComparable ctx.types tb then
        if !ta.comparable ctx.types then eerr p (notComparable ctx.types ta s!"an operand of '{op}'")
        if !tb.comparable ctx.types then eerr p (notComparable ctx.types tb s!"an operand of '{op}'")
        eerr p "these values cannot be compared"
      -- different types with the same Verse Core type (a char32 or an enum
      -- and an int, two structs with the same fields, also inside
      -- containers) would compare equal there
      -- (or could be, at some instance of the type parameters they mention:
      -- two different ones, or one and a type that several types share in
      -- Core, one with an int or a tuple)
      let (va, vb) := (ta.toVTy ctx.types, tb.toVTy ctx.types)
      let (pa, pb) := (!ta.params.isEmpty, !tb.params.isEmpty)
      if !(ta == tb) && ta != .never && tb != .never &&
          (va == vb || (pa && pb) || (pa && vb.shared) || (pb && va.shared)) then
        eerr p s!"'{op}' compares values of different types, {ta.show} and {tb.show}"
      -- (nor an int with a rational inside containers, #116: equal values
      -- that Verse Core holds differently, `1` and `(1, 1)`)
      if ratMismatch ta tb then
        eerr p s!"'{op}' compares values of different types, {ta.show} and {tb.show} (an int and a rational inside them: convert the ints first)"
      if scalarMismatch ta tb then
        eerr p s!"'{op}' compares values of different types, {ta.show} and {tb.show}"
    else if !((ta == .int && tb == .int) || (ta == .char && tb == .char) || (ta == .char32 && tb == .char32) ||
        (ta == .float && tb == .float)) then
      eerr p s!"'{op}' compares ints, chars, char32s or floats, found {ta.show} and {tb.show}"
  let accepts : Ty → Bool := fun ty => arithmeticType ctx.types ty || ty == .char || ty == .char32
  let numeric (value : R) : EM R := do
    return widenR ctx.types (← elabValueViewWith elabE ctx p value accepts "comparison")
  let source := widenR ctx.types (← elabE ctx a none)
  let view ← match ctx.valueView p source.ty accepts "comparison" with
    | .ok view => pure view
    | .error message => throw message
  let (ra, original) ← match view with
    | none => pure (source, none)
    | some _ => do
      let slot ← fresh source.ty
      let converted ← numeric ⟨.local slot, source.ty⟩
      pure (⟨.seq (.assign slot source.e) converted.e, converted.ty⟩, some (slot, source.ty))
  let result (code : Expr) (ty : Ty) : R := match original with
    | some (slot, ty) => ⟨.seq code (.local slot), ty⟩
    | none => ⟨code, ty⟩
  -- (an array and a tuple compare as arrays: the tuple is converted)
  let asArr (r : R) (other : Ty) : EM R := do
    match r.ty, other with
    | .tup _, .arr _ => return ⟨← coerce p r other, other⟩
    | _, _ => return r
  match rest with
  | [(op, b)] =>
    let rb ← numeric (← elabE ctx b (some ra.ty))
    if ra.ty == .rational || rb.ty == .rational then
      let ta ← fresh ra.ty
      let tb ← fresh rb.ty
      let test ← ratTest ctx p op ⟨.local ta, ra.ty⟩ ⟨.local tb, rb.ty⟩
      return result (.seq (.assign ta ra.e) (.seq (.assign tb rb.e) (.seq test (.local ta)))) ra.ty
    let ra ← asArr ra rb.ty
    let rb ← asArr rb ra.ty
    checkTys op ra.ty rb.ty
    return result (p2 (ordOf op ra.ty) ra.e rb.e) ra.ty
  | _ =>
    -- a chain: each operand is evaluated once, every adjacent pair is checked,
    -- and the result is the leftmost operand (Book of Verse §5.4)
    let t0 ← fresh ra.ty
    let mut prev := t0
    let mut prevTy := ra.ty
    let mut steps : Array Expr := #[.assign t0 ra.e]
    for (op, b) in rest do
      let rb ← numeric (← elabE ctx b (some prevTy))
      let rb ← asArr rb prevTy
      -- (the previous operand, as an array when this one is)
      let prevE ← match prevTy, rb.ty with
        | .tup _, .arr _ => coerce p ⟨.local prev, prevTy⟩ rb.ty
        | _, _ => pure (.local prev)
      let tb ← fresh rb.ty
      if prevTy == .rational || rb.ty == .rational then
        steps := steps.push (.assign tb rb.e)
        steps := steps.push (← ratTest ctx p op ⟨.local prev, prevTy⟩ ⟨.local tb, rb.ty⟩)
      else
        checkTys op (match prevTy, rb.ty with | .tup _, .arr _ => rb.ty | _, _ => prevTy) rb.ty
        steps := steps.push (.assign tb rb.e)
        steps := steps.push (p2 (ordOf op prevTy) prevE (.local tb))
      prev := tb
      prevTy := rb.ty
    return result (steps.foldr Expr.seq (.local t0)) ra.ty

/-- `elabSetWith`, given this block's functions (#325). -/
partial def elabSet (ctx : Ctx) (p : Pos) (lhs0 : SExpr) (op : Option String) (rhs0 : SExpr) : EM R := do
  let rec firstField : SExpr → Option (String × String)
    | .member _ (.ident _ root) field => some (root, field)
    | .member _ receiver _ | .app _ receiver _ true | .query _ receiver => firstField receiver
    | _ => none
  if let some (root, field) := firstField lhs0 then
    if let some binding := ctx.lookup root then
      if let .param .. := binding.ty then
        let receiver ← elabBoundReceiver ctx p ⟨.local binding.slot, binding.ty⟩ field
        if receiver.ty != binding.ty then
          let slot ← fresh receiver.ty
          let name := s!"$subtypeSet{slot}"
          let rec replaceRoot : SExpr → SExpr
            | .ident q n => if n == root then .ident q name else .ident q n
            | .member q value member => .member q (replaceRoot value) member
            | .app q value args true => .app q (replaceRoot value) args true
            | .query q value => .query q (replaceRoot value)
            | value => value
          let inner := { ctx with locals := { name, slot, ty := receiver.ty, mutable := false } :: ctx.locals }
          let direct := match lhs0 with | .member _ (.ident _ _) _ => true | _ => false
          let rootPrelude := if direct then none else some (name, receiver.e)
          let result ← elabSetWith elabE (fun c q r m => elabMember c q r m) inner p (replaceRoot lhs0) op rhs0 rootPrelude
          return ⟨if direct then .seq (.assign slot receiver.e) result.e else result.e, result.ty⟩
  elabSetWith elabE (fun c q r m => elabMember c q r m) ctx p lhs0 op rhs0

/-- `for` (#208, #314): `elabForWith`, given this block's functions (#325). -/
partial def elabFor (ctx : Ctx) (p : Pos) (clauses : List SExpr) (body : SExpr) (prepared : Bool := false)
    (firstDecides : Bool := false) (failure : Option SExpr := none) : EM R :=
  elabForWith elabAlts (fun c q i t pl => elabBranchAlts c q i t pl) elabE elabInts elabLoopGen elabSeq ctx p clauses body
    prepared firstDecides failure

/-- A condition's local types under its cast refinements. Its code is used
    only by the isolated branch-type probe. -/
partial def elabChoiceTypeCondition (ctx : Ctx) : List SExpr → EM (R × Ctx × Bool)
  | [] => pure (⟨.lit .void, .void⟩, ctx, false)
  | cl :: rest => do
    if let .decl p d none false (.app _ (.ident _ target) [x] true) := cl then
      let st ← get
      let rx ← elabE ctx x none
      let env := ctx.types
      if let some (source, _, targs, _, eqs, opened) := refiningCast? env target rx.ty (env.tvars.map (·.1)) then
        if env.isRefClass source && (opened.isEmpty || env.isRefClass target) then
          if let some (μ, opened) := castRefinement? env eqs opened (env.comparableArgs target targs) then
            let targs := targs.map fun t => t.subst (opened.filterMap fun (n, _, c) => if c then some (n, Ty.param n true) else none)
            let refine (t : Ty) := t.subst μ
            let ty := refine (.struct target targs)
            let slot ← fresh ty
            let c : Ctx := { ctx with
              locals := { name := d, slot, ty, mutable := false } :: (ctx.locals.map fun l => { l with ty := refine l.ty }),
              types := { env with tvars := (env.tvars.map (fun (n, t) => (n, refine t)) ++
                opened.map (fun (n, _, cmp) => (n, Ty.param n cmp))) } }
            let (r, c, _) ← elabChoiceTypeCondition c rest
            return (⟨.seq Expr.failV r.e, r.ty⟩, c, true)
      set st
    let (r, c) ← if Choice.hasChoice [cl] (choiceOrder ctx) then elabOneClauses ctx [cl]
      else elabSeq ctx [cl] none
    let (tail, c, refined) ← elabChoiceTypeCondition c rest
    return (⟨.seq r.e tail.e, tail.ty⟩, c, refined)

/-- An `if … else if … else …` with choices in its branches (#235): code that
    picks the branch, once, into a fresh slot (each condition a failure
    context of its own, tried when the ones before failed), and every
    branch's alternatives guarded by it (`B = j; a`), each seeing the names
    its conditions bind, at their written type or their join. -/
partial def elabBranchAlts (ctx : Ctx) (p : Pos) (i : SExpr) (sty : Option STy) (place : Option SExpr := none) :
    EM (Option Expr × Ty × List Expr × Bool) := do
  let i := pruneMethodCases ctx i
  let arms := Choice.arms i
  let bi ← fresh .int
  let mut conds : Array (Option Expr) := #[]
  let mut ctxs : Array Ctx := #[]
  let mut refined := false
  for (cs?, _) in arms do
    match cs? with
    | some cs =>
      let (rc, cT, refines) ← if ctx.typeOnly && choiceHasCast ctx i then
          elabChoiceTypeCondition { ctx with canFail := true, inTaking := true } cs
        else do
          let (rc, cT) ← if Choice.hasChoice cs (choiceOrder ctx) then elabOneClauses { ctx with canFail := true } cs
            else elabSeq { ctx with canFail := true, inTaking := true } cs none
          pure (rc, cT, false)
      refined := refined || refines
      if !(rc.e.mayFail ctx.sigProg) && (← ctx.failabilityKnown) then
        eerr p "the condition of this if cannot fail (Verse requires a failable condition)"
      conds := conds.push (some rc.e)
      ctxs := ctxs.push { cT with canFail := ctx.canFail, inTaking := ctx.inTaking }
    | none =>
      conds := conds.push none
      ctxs := ctxs.push ctx
  -- (from the last branch back: `if (c₀) then B := 0 else if (c₁) then B := 1 … else B := n`)
  let setB (j : Nat) : Expr := .assign bi (.lit (.int j))
  let pick := (conds.toList.zipIdx).foldr (fun (c?, j) acc => match c? with
    | some c => Expr.ite c (setB j) acc
    | none => setB j) (.lit .void)
  -- (the written type, or for `set L = if …` the type of `L`)
  let t? ← match ← sty.mapM (resolveTy ctx.types p) with
    | some t => pure (some t)
    | none => match place with
      | some l => tryCatch (do pure (some (← elabE ctx l none).ty)) fun _ => pure none
      | none => pure none
  -- (for the type only, #283: a value with a call with several values or a
  -- choice in it, which only a failure context that takes its values
  -- compiles, at the type of those values, as `option{…}` takes them)
  let elabA (c : Ctx) (a : SExpr) (t? : Option Ty) : EM R := do
    let wanted := t?
    let t? := if ctx.typeOnly then t?.map (·.subst c.types.tvars) else t?
    let r ← if ctx.typeOnly && Choice.hasLiftable a then do
      -- (a block's last value at the expected type, which `option{…}`
      -- does not pass into it, #383's review: `{ …; false }` against ?int;
      -- its `defer:`s after the value, as where it is lifted, #283, since
      -- the braces of `option{…}` hold clauses)
      let a := match a with
        | .block bp ss => SExpr.block bp (Choice.deferLast bp "$jdv" ss)
        | a => a
      let a := match a, t? with
        | .block bp ss@(_ :: _), some t =>
          SExpr.block bp (ss.dropLast ++ [.decl bp "$jv" (some t.toSTy) false (ss.getLast?.getD (.tuple bp [])), .ident bp "$jv"])
        | a, _ => a
      let r ← elabE c (.optionLit a.pos a) (t?.map .opt)
      match r.ty with
      | .opt t => pure ⟨r.e, t⟩
      | _ => pure r
    else elabE c a t?
    if ctx.typeOnly then
      if let some t := t? then discard <| coerce a.pos r t
    -- Report the original scope's bounds to the outer consumer. The arm's
    -- local comparable evidence must not constrain an unrefined else path.
    let bounds := Ty.mergeParamBounds ((ctx.types.tvars.map (·.2) ++ ctx.locals.map (·.ty)).flatMap Ty.paramsC)
    return { r with ty := if ctx.typeOnly then (wanted.getD r.ty).withParamBounds bounds else r.ty }
  let all : List (Nat × SExpr) := arms.zipIdx.flatMap fun ((_, arm), j) => ((Choice.alts? arm).getD [arm]).map (j, ·)
  -- (#366, the state before the alternatives, for the retries below)
  let st0 ← get
  let mut rs : Array (Nat × SExpr × R) := #[]
  for ((_, arm), j) in arms.zipIdx do
    let c := ctxs.getD j ctx
    for a in (Choice.alts? arm).getD [arm] do
      -- (without a type, each later one against the first's, else on its
      -- own, as `elabAlts` does, #32)
      let r ← match t?, rs[0]? with
        | some t, _ => elabA c a (some t)
        | none, none => do
          -- (#366) when the first needs another's type (`array{}` first):
          -- the first later one with a type on its own gives it; else the
          -- first one's own error, as before
          match ← tryCatch (do pure (Except.ok (← elabA c a none))) (fun e => pure (Except.error e)) with
          | .ok r => pure r
          | .error err =>
            if ctx.retries ≥ 3 then throw err
            let st ← get
            let mut ref? : Option Ty := none
            for (j', a') in all.drop 1 do
              if ref?.isSome then continue
              if let some r' ← tryCatch (do pure (some (← elabA { (ctxs.getD j' ctx) with retries := ctx.retries + 1 } a' none))) (fun _ => pure none) then
                ref? := some r'.ty
            set st
            match ref? with
            | some rt => elabA { c with retries := ctx.retries + 1 } a (some rt)
            | none => throw err
        | none, some (_, _, r0) =>
          if c.retries ≥ 3 then tryCatch (elabA c a none) fun _ => elabA c a (some r0.ty)
          else
            let c2 := { c with retries := c.retries + 1 }
            tryCatch (elabA c2 a (some r0.ty)) fun _ => elabA c2 a none
      rs := rs.push (j, a, r)
  let some (_, _, r0) := rs[0]? | eerr p "internal: an if without branches"
  let mut ty ← match t? with
    | some t => pure t
    | none => rs.toList.foldlM (fun acc (_, _, r) => join p acc r.ty none) r0.ty
  if ty == .never then eerr p "cannot infer the type of this if's choices"
  -- (#366) with nothing in common, every alternative against a later
  -- one's type instead, the first that fits them all, as `elabAlts` does
  if t?.isNone && ty == .any && ctx.retries < 3 then
    let env := (← get).env
    let mut found := false
    let stAfter ← get
    for (_, _, r) in rs.toList.drop 1 do
      if found || r.ty == .any || r.ty == .never then continue
      -- (from the state before the alternatives: the first try's code and
      -- slots are not kept)
      set st0
      let attempt : EM (Array (Nat × SExpr × R)) := rs.mapM fun (j, a, _) => do
        let c := ctxs.getD j ctx
        return (j, a, ← elabA { c with retries := ctx.retries + 1 } a (some r.ty))
      match ← tryCatch (do pure (some (← attempt))) (fun _ => pure none) with
      | some rs' =>
        match rs'.toList.foldl (fun acc (_, _, r') => acc.bind fun t => joinTy env t r'.ty none) (some r.ty) with
        | some ty' =>
          if ty' != .any then
            ty := ty'; rs := rs'; found := true
          else set stAfter
        | none => set stAfter
      | none => set stAfter
  let es ← rs.toList.mapM fun (j, a, r) => do
    return Expr.seq (.prim .eq [.local bi, .lit (.int j)]) (← coerce a.pos r ty)
  return (some pick, ty, es, refined)

/-- The alternatives of a choice (#208), at its written type or at their
    join (each one against the first's type, else on its own, as `if`'s
    branches are), and that type. -/
partial def elabAlts (ctx : Ctx) (p : Pos) (b : Choice.Binding) : EM (Ty × List Expr) := do
  -- (a choice or a call with several values left in an alternative is in a
  -- failure context that takes values, where it cannot be lifted from)
  let ctx := { ctx with inTaking := true }
  let alts := b.alts
  -- (the written type, or for `set L = a | b` the type of `L`)
  let t? ← match ← b.ty.mapM (resolveTy ctx.types p) with
    | some t => pure (some t)
    | none => match b.place with
      | some l => tryCatch (do pure (some (← elabE ctx l none).ty)) fun _ => pure none
      | none => pure none
  match t? with
  | some t => return (t, ← alts.mapM fun a => do coerce a.pos (← elabE ctx a (some t)) t)
  | none =>
    let some a0 := alts.head? | eerr p "internal: a choice without alternatives"
    -- (#366) a first alternative that needs another's type (`array{} | …`):
    -- a later one on its own, then all against its type; when none fits,
    -- the first one's own error, as before
    let st0 ← get
    let r0? ← tryCatch (do pure (Except.ok (← elabE ctx a0 none))) fun e => pure (Except.error e)
    let r0 ← match r0? with
      | .ok r => pure r
      | .error err =>
        if ctx.retries ≥ 3 then throw err
        let c2 := { ctx with retries := ctx.retries + 1 }
        for a in alts.tail do
          let res ← tryCatch (do
              let ra ← elabE c2 a none
              let rs' ← alts.mapM fun a' => elabE c2 a' (some ra.ty)
              let ty ← rs'.foldlM (fun acc r => join p acc r.ty none) ra.ty
              pure (some (ty, ← ((alts.zip rs').mapM fun (a', r) => coerce a'.pos r ty)))) fun _ => pure none
          if let some out := res then return out
        throw err
    -- (each later one against the first's type, else on its own, to join;
    -- a few levels deep, then on its own first, as the join needs, #32)
    let rs ← alts.tail.mapM fun a =>
      if ctx.retries ≥ 3 then tryCatch (elabE ctx a none) fun _ => elabE ctx a (some r0.ty)
      else
        let c2 := { ctx with retries := ctx.retries + 1 }
        tryCatch (elabE c2 a (some r0.ty)) fun _ => elabE c2 a none
    let ty ← rs.foldlM (fun acc r => join p acc r.ty none) r0.ty
    if ty == .never then eerr p "cannot infer the type of this choice"
    -- (#366) with nothing in common, every alternative against a later
    -- one's type instead, the first that fits them all: `false | option{4}`
    -- is a `?int`, as `option{4} | false` is; else `any`, as before
    if ty == .any && ctx.retries < 3 then
      let env := (← get).env
      let stAfter ← get
      for r in rs do
        if r.ty == .any || r.ty == .never then continue
        -- (from the state before the alternatives: the first try's code and
        -- slots are not kept)
        set st0
        let c2 := { ctx with retries := ctx.retries + 1 }
        match ← tryCatch (do pure (some (← alts.mapM fun a => elabE c2 a (some r.ty)))) (fun _ => pure none) with
        | some rs' =>
          match rs'.foldl (fun acc r' => acc.bind fun t => joinTy env t r'.ty none) (some r.ty) with
          | some ty' =>
            if ty' != .any then
              return (ty', ← ((alts.zip rs').mapM fun (a, r') => coerce a.pos r' ty'))
            set stAfter
          | none => set stAfter
        | none => set stAfter
    return (ty, ← ((alts.zip (r0 :: rs)).mapM fun (a, r) => coerce a.pos r ty))

/-- The clauses of a failure context that takes its first success (an `if`
    condition, `first{…}`), when one of them binds a choice (#208):
    `Expr.firstE` over the clauses, each choice an `Expr.chooseFirst` around
    the clauses after it, which `break` when all of them succeed. Its value is
    `void`: an `if` and `first{…}` read their clauses' values through names. -/
partial def elabOneClauses (ctx : Ctx) (cs : List SExpr) : EM (R × Ctx) := do
  let ctx := { ctx with liftWhy := "" }
  let (code, ctx') ← elabFirstGo ctx
    (Choice.prepare cs (choiceValues ctx) (choiceField ctx) (fieldOrder := choiceOrder ctx)
      (keepBranches := choiceHasCast ctx))
  return (⟨code, .void⟩, ctx')

/-- `Expr.firstE` of the code of clauses lifted already (`elabOneGo`), and
    the context after them. `firstE`'s loop takes the `break` that ends a
    success, so a source `break` in them that leaves them for the enclosing
    loop (#283) sets that loop's break flag first, `Ctx.forBreakSlot`, as one
    in a `for`'s filters does, after the cleanup it leaves; the flag then
    breaks again after `firstE`, so a break keeps what the clauses did up to
    it, as with no choice. One that leaves as an exit packet
    (`forBreakCapture`, `refineExits`) returns, through any loop. -/
partial def elabFirstGo (ctx : Ctx) (cs : List SExpr) : EM (Expr × Ctx) := do
  let after (c : Ctx) : Ctx := { c with
    inLoop := ctx.inLoop, inChoice := ctx.inChoice, inTaking := ctx.inTaking, forBreakSlot := ctx.forBreakSlot }
  if !ctx.inLoop || !firstBreaks cs then
    -- (with no loop, a `break` is refused where it is; `inChoice` says
    -- that none is expected here)
    let (code, c) ← elabOneGo { ctx with inLoop := false, inChoice := ctx.inLoop, inTaking := true } cs
    return (Expr.firstE code, after c)
  if ctx.forBreakCapture.isSome || ctx.refineExits.brk.isSome then
    let (code, c) ← elabOneGo { ctx with inTaking := true } cs
    return (Expr.firstE code, after c)
  -- (a `for` around these clauses has made the flag already, and resets it)
  let flag ← match ctx.forBreakSlot with
    | some flag => pure flag
    | none => fresh .logic
  let (code, c) ← elabOneGo { ctx with inTaking := true, forBreakSlot := some flag } cs
  let code := Expr.seq (Expr.firstE code) (forwardSourceBreak flag (.lit .void))
  return (if ctx.forBreakSlot.isNone then .seq (.assign flag (.lit (.logic false))) code else code, after c)

partial def elabOneGo (ctx : Ctx) : List SExpr → EM (Expr × Ctx)
  | [] => return (Expr.brkV, ctx)
  | cl :: rest => do
    if let .app p (.ident _ "$defer") _ _ := cl then
      eerr p "defer: cannot be a clause of an if condition or first{…} that has a choice (#208)"
    -- (#283) the choice of an `if`'s branches, each guarded by its branch
    -- (`Choice.prepare`), with no type written: at the branches' join, as
    -- the `if`'s value has, found by elaborating the `if` apart for the type
    -- only, `$joinOf` (for `set L = if …`, at `L`'s type)
    let cl ← match cl with
      | .decl p x none false (.app q f@(.ident _ "$choice") as false) =>
        match ← joinOfType (fun c pos i t pl => elabBranchAlts c pos i t pl) ctx p as with
        | some ty => pure (.decl p x (some ty) false (.app q f (as.filter (!Choice.isJoinOf ·)) false))
        | none => pure cl
      | cl => pure cl
    let cl := pruneMethodBinding ctx cl
    if let some b@{ branchy := some i, .. } := Choice.binding? cl then
      if choiceHasCast ctx i then
        let p := b.pos
        let t := s!"$refineChoice{p.line}_{p.col}{b.name}"
        -- Infer the element type before putting the remaining clauses in
        -- the branch. Each option takes the branch's first value for types.
        let st ← get
        let (_, ty, _, refined) ← elabBranchAlts { ctx with typeOnly := true } p i b.ty b.place
        restoreConstructProbe ctx st
        if !refined then
          if Choice.plainBranches Choice.hasLiftable i then
            return ← elabOneChoice ctx b rest
          -- (#283) one with nothing left to lift, the cases its receiver's
          -- type rules out dropped (`pruneMethodBinding`): an `if` of one
          -- value, bound as any (`prepare` would give it back as it is)
          if b.place.isNone && !Choice.hasLiftable i then
            return ← elabOneGo ctx (.decl p b.name b.ty false i :: rest)
          return ← elabOneGo ctx (Choice.prepare [cl] (choiceValues ctx) (choiceField ctx)
            (site := b.name) (fieldOrder := choiceOrder ctx) ++ rest)
        if ctx.typeOnly then
          checkNewLocal ctx p b.name
          let slot ← fresh ty
          return ← elabOneGo { ctx with locals := { name := b.name, slot, ty, mutable := false } :: ctx.locals } rest
        let key := contKey ctx p b.name (i :: rest) ++ firstReturnKey ctx rest
        let request := ctx.types.requests.loops.find? (·.key == key)
        let hasLater := rest.any fun cl => match Choice.binding? cl with
          | some { branchy := some next, .. } => choiceHasCast ctx next
          | some { alts, .. } => alts.any Choice.hasLiftable
          | none => false
        if request.isNone && hasLater then
          let st0 ← get
          let slot ← fresh ty
          let c := { ctx.withTrial .continuation with locals := { name := b.name, slot, ty, mutable := false } :: ctx.locals }
          let (code, c2) ← elabOneGo c rest
          let fx := (← get).fx
          match contLiftOf ctx c2 p b.name [i] rest fx with
          | .ok lift =>
            askHelper p lift
            -- (what follows the clauses is not the trial's)
            return (code, { c2 with trial := ctx.trial })
          | .error _ => set st0
        let request := request.filter fun l =>
          ctx.acceptsHelper l
        let binds := (b.name :: Choice.boundIn rest).eraseDups
        let vars := rest.filterMap fun | .decl _ n _ true _ => some n | _ => none
        let tup := SExpr.tuple p (binds.map (SExpr.ident p ·) ++ [.ident p "true"])
        let consume (arm : SExpr) : SExpr :=
          let clauses := Choice.prepare [.decl p b.name (some ty.toSTy) false arm]
            (choiceValues ctx) (choiceField ctx) (site := t) (fieldOrder := choiceOrder ctx)
            (keepBranches := choiceHasCast ctx)
          let tail := match request with
            | some l =>
              -- The continuation is part of the search, before firstP
              -- commits this value. Failure must retry the next alternative.
              let result := t ++ "$continuation"
              [.decl p result none false (.app p (.ident p l.name) l.args true), .ident p result]
            | none => rest ++ [tup]
          .optionLit p (.app p (.ident p "$firstP") [.block p (clauses ++ tail)] false)
        let selected := Choice.consumeBranches i t consume
        -- A selected branch with no successful value gives none. Query it
        -- after selection so an alternative's failure cannot select else.
        let get (j : Nat) := SExpr.app p (.ident p t) [.int p (j : Int)] false
        let unpack := binds.zipIdx.map fun (n, j) => SExpr.decl p n none (vars.contains n) (get j)
        let writes := request.toList.flatMap fun l => l.sets.zipIdx.map fun (n, j) =>
          SExpr.set p (.ident p n) none (get (l.binds.length + j))
        let unpack := match request with
          | some l => firstUnpack p l t
          | none => unpack ++ writes
        let (code, c) ← elabOneGo ctx ([.decl p t none false (.query p selected)] ++ unpack)
        return (code, { c with inlineScopes := Choice.inlineScopesAfter ctx.inlineScopes rest })
    match Choice.binding? cl with
    | some b@{ each := some (.app _ (.ident _ "$loop") lp false), .. } =>
      -- (one taken lazily, #246: a loop over its values, each followed by
      -- the clauses after it, which leave the loop when they succeed; the
      -- code after the loop says whether one did)
      let p := b.pos
      let g := match lp with | .ident _ g :: _ => g | _ => ""
      -- (when what it runs once for all the values of an item has effects,
      -- asked for by an earlier elaboration: a call of a function of its
      -- own that runs the clauses after it too, then the names they bind)
      if let some l := (if ctx.typeOnly then none else ctx.types.requests.loops.find? (·.key == firstKey ctx p lp b.name b.ty rest)) then
        let t := s!"$ft{p.line}_{p.col}"
        let (code, c) ← elabOneGo ctx ([.decl p t none false (.app p (.ident p l.name) l.args true)] ++
          firstUnpack p l t)
        return (code, { c with inlineScopes := Choice.inlineScopesAfter ctx.inlineScopes rest })
      let fx0 := (← get).fx
      modify fun st => { st with fx := [] }
      let lg ← elabLoopGen ctx p lp
      let ty ← match ← b.ty.mapM (resolveTy ctx.types p) with
        | some t => pure t
        | none => pure lg.vty
      checkNewLocal ctx p b.name
      let x ← fresh ty
      let c1 := { ctx with locals := { name := b.name, slot := x, ty, mutable := false } :: ctx.locals }
      let (inner, c2) ← elabOneGo c1 rest
      let fxB := (← get).fx
      modify fun st => { st with fx := fx0 }
      for (k, q, via) in fxB do noteFx q [k] via
      let isS (f : Nat) : Bool := ctx.sigs.any fun s => s.idx == f && s.suspends
      -- (the values at the function's result type, at the type arguments
      -- this call gives, for a generic one)
      let lift := firstLiftOf ctx c2 p g lp b.name b.ty rest fxB (ctx.suspends && Suspend.hasSusp isS inner) lg.vty lg.instances
        lg.frames lg.kTy lg.frameTys
      modify fun st => { st with loopFirst := st.loopFirst ++
        [{ g, pos := p, itemCode := lg.itemCode, argSet := lg.argSet, lift }] }
      let bindX ← coerce p ⟨lg.value, lg.vty⟩ ty
      let done ← fresh .logic
      let vd : Expr := .lit .void
      let take : Expr := .ite (.seq (.assign x bindX) (.seq inner Expr.failV)) vd vd
      -- (#283) a value that comes to a continuation member's choice point
      -- breaks out of `take`, keeping what it did, with `bnd` set; so does
      -- a success (or a source break), with it unset, which leaves the loop
      let take : Expr := match lg.bnd with
        | some b => .seq (.assign b (.lit (.logic false)))
            (.seq (.loop (.seq take (.seq (.assign b (.lit (.logic true))) Expr.brkV)))
              (.ite (.prim .query [.local b]) vd Expr.brkV))
        | none => take
      let body : Expr := .seq
        (.ite (p2 .eq (.local lg.sp) (.lit (.int 0))) (.seq (.assign done (.lit (.logic true))) Expr.brkV) vd)
        (.seq lg.step (.ite (.prim .query [.local lg.has])
          (.seq take lg.after) vd))
      return (.seq lg.init (.seq (.assign done (.lit (.logic false))) (.seq (.loop body)
        (.ite (p2 .eq (.local done) (.lit (.logic false))) Expr.brkV vd))), c2)
    | some b@{ each := some arr, .. } =>
      -- (a call of a recursive function with several values, #235: each
      -- element of the array of its values in turn, the clauses after it
      -- in the filter, as `chooseFirst` does with alternatives)
      let p := b.pos
      let ra ← elabE ctx arr none
      let ety ← match ra.ty with
        | .arr t => pure t
        | t => eerr p s!"internal: the values of a call are {t.show}"
      let ty ← match ← b.ty.mapM (resolveTy ctx.types p) with
        | some t => pure t
        | none => pure ety
      checkNewLocal ctx p b.name
      let e ← fresh ety
      let x ← fresh ty
      let c1 := { ctx with locals := { name := b.name, slot := x, ty, mutable := false } :: ctx.locals }
      let (inner, c2) ← elabOneGo c1 rest
      let bindX ← coerce p ⟨.local e, ety⟩ ty
      return (.forE e ra.e (.seq (.assign x bindX) (.seq inner Expr.failV)) (.lit .void), c2)
    | some b@{ place := none, branchy := none, each := none, .. } =>
      if b.alts.any Choice.hasLiftable then
        -- (a choice whose alternatives have several values themselves, or
        -- clauses to lift, #283: each alternative with the clauses after
        -- it, in a first{…} of its own, so that its values are taken in
        -- order and the clauses run for each; the first success gives the
        -- names they bind, in a tuple)
        let p := b.pos
        let finish (action : EM (Expr × Ctx)) : EM (Expr × Ctx) := do
          let (code, c) ← action
          return (code, { c with inlineScopes := Choice.inlineScopesAfter ctx.inlineScopes rest })
        -- (with the binding's name: an inlined body's position is every
        -- site's, #314)
        let t := s!"$ct{p.line}_{p.col}{b.name}"
        let binds := (b.name :: Choice.boundIn rest).eraseDups
        let vars := rest.filterMap fun | .decl _ n _ true _ => some n | _ => none
        let tup : SExpr := .tuple p (binds.map (SExpr.ident p ·) ++ [.ident p "true"])
        let liftAlt (a : SExpr) (i : Nat) : List SExpr :=
          Choice.prepare [.decl p b.name b.ty false a] (choiceValues ctx) (choiceField ctx)
            (fieldOrder := choiceOrder ctx)
            (site := s!"{t}a{i}") (keepBranches := choiceHasCast ctx)
        let alt (a : SExpr) (i : Nat) : SExpr :=
          .app p (.ident p "$firstP") [.block p (liftAlt a i ++ rest ++ [tup])] false
        let copied : List SExpr := [.decl p t none false (Choice.mk p (b.alts.zipIdx.map fun (a, i) => alt a i))] ++
          binds.zipIdx.map fun (n, i) => .decl p n none (vars.contains n) (.app p (.ident p t) [.int p (i : Int)] false)
        -- (#335: another such choice in the clauses after it: those clauses a
        -- function of their own, which each alternative calls, instead of a
        -- copy in each, which doubled the code with each such choice)
        let isComposed (c : SExpr) : Bool := match Choice.binding? c with
          -- A later typed dispatch stays a branch binding until its
          -- receiver prefix is elaborated. Its lifted arms would copy
          -- this same suffix once prepared, just as composed alternatives do.
          | some { branchy := some i, .. } => !Choice.plainBranches Choice.hasLiftable i
          | some b => b.composed
          | none => false
        if !b.alts.isEmpty then
          let req := if ctx.typeOnly then none else ctx.types.requests.loops.find? (·.key == contKey ctx p b.name (b.alts ++ rest) ++ firstReturnKey ctx rest)
          -- (asked for where more effects are allowed than here, as in a
          -- function of its own of a call taken lazily, #246: copied)
          let fits (l : Choice.FirstLift) : Bool :=
            ctx.acceptsHelper l
          if let some l := req then
            if !fits l then return ← finish (elabOneGo ctx copied)
            -- (the call a clause, whose failure goes back into the
            -- alternative's own choices, then its tuple the value)
            let kt := s!"{t}k"
            let altK (a : SExpr) (i : Nat) : SExpr :=
              .app p (.ident p "$firstP") [.block p (liftAlt a i ++ (l.casePrelude[i]?.getD []) ++
                continuationBind p l kt (.app p (.ident p l.name) l.args true) ++ [.ident p kt])] false
            return ← finish (elabOneGo ctx ([.decl p t none false (Choice.mk p (b.alts.zipIdx.map fun (a, i) => altK a i))] ++
              firstUnpack p l t))
          -- (the first elaboration: one alternative with the clauses after it,
          -- for their names' types and effects, and the function asked for;
          -- its code is not kept, as the next elaboration has the function)
          if let some a0 := b.alts.head? then
            let st0 ← get
            let fx0 := st0.fx
            modify fun st => { st with fx := [] }
            -- (each other alternative alone, without the clauses after it: its
            -- value's type, which must be the first's, as the function takes
            -- one; and the continuations in it, asked for in this elaboration
            -- too, so that nesting takes no more elaborations)
            let mut tys : List Ty := []
            for (a, i) in b.alts.zipIdx do
              let r ← elabE { ctx with canFail := true, inTaking := true }
                (.app p (.ident p "$firstP") [.block p (liftAlt a i ++ [.ident p b.name])] false) none
              tys := tys ++ [r.ty]
            let same := tys.all (some · == tys.head?)
            let prefixState ← get
            -- (what refuses it known before the trial, which then costs nothing)
            let ok := same && rest.any isComposed
            let (code1, c1) ← if ok then elabOneGo (ctx.withTrial .continuation) ([.decl p t none false (alt a0 0)] ++
                binds.zipIdx.map fun (n, i) => .decl p n none (vars.contains n) (.app p (.ident p t) [.int p (i : Int)] false))
              else pure (Expr.lit .void, ctx)
            -- (what follows the clauses is not the trial's)
            let c1 := { c1 with trial := ctx.trial }
            let fxB := (← get).fx
            match (if ok then contLiftOf ctx c1 p b.name b.alts rest fxB else .error "alternatives of different types") with
            | .ok lift =>
              modify fun st => { st with fx := fx0 }
              askHelper p lift
              for (k, q, via) in fxB do noteFx q [k] via
              return ← finish (pure (code1, c1))
            | .error _ => set st0
            if !same && !ctx.constructProbe then
              let stem := s!"$choiceType{(contKey ctx p b.name (b.alts ++ rest)).hash}"
              if let some plan := choiceTypePlan ctx stem b.name tys rest then
                set { prefixState with fx := [] }
                let trial ← tryCatch (do
                  let operations ← choiceOperations elabE ctx stem b.name plan rest
                  let plan := operations.plan
                  let poly ← operations.context (← choiceTypeContext ctx plan)
                  let slot ← fresh plan.binding
                  let bound := { poly with
                    typeOnly := true,
                    locals := { name := b.name, slot, ty := plan.binding, mutable := false } :: poly.locals }
                  let (_, c2) ← elabOneGo bound (rest.map operations.rewrite)
                  let effects := (← get).fx
                  let lift ← match contLiftOf poly c2 p b.name b.alts (rest.map operations.rewrite) effects with
                    | .ok lift =>
                      let key := contKey ctx p b.name (b.alts ++ rest) ++ firstReturnKey ctx rest
                      joinedChoiceResult poly plan (operations.lift key lift)
                    | .error _ => return none
                  return some (lift, effects)) (fun _ => pure none)
                set prefixState
                if let some (lift, effects) := trial then
                  modify fun st => { st with fx := fx0 }
                  askHelper p lift
                  for (k, q, via) in prefixState.fx ++ effects do noteFx q [k] via
                  let packetTy ← resolveTy ctx.types p (lift.joinedRet.getD lift.ret)
                  let packet ← fresh packetTy
                  let name := t ++ "$probe"
                  let bound := { ctx with locals := { name, slot := packet, ty := packetTy, mutable := false } :: ctx.locals }
                  let (_, result) ← elabOneGo bound (firstUnpack p lift name)
                  return ← finish (pure (.prim .userErr [], { result with locals := result.locals.filter (·.name != name) }))
                set st0
              -- (#283, #335) not shared, so copied for each value's type:
              -- where the first success is taken, what they bind has one
              -- type after them, which values with nothing above both lack
              if let t0 :: ts := tys then
                if (ts.foldlM (fun acc ty => joinTy ctx.types acc ty none) t0).isNone then
                  let other := (ts.find? (· != t0)).getD t0
                  let what := if b.name.startsWith "$" then "its value" else b.name
                  eerr p s!"the values of this choice are of types with nothing above both, {t0.show} and {other.show}, and the clauses after it cannot be shared by them (#335): copied for each, {what} would have no one type after them, where the first success is taken: not supported yet (#283); take the values in a for, or make in each alternative what needs its own type"
        return ← finish (elabOneGo ctx copied)
      let p := b.pos
      let n := b.name
      let (ty, es) ← elabAlts ctx p b
      checkNewLocal ctx p n
      let k ← fresh .int
      let x ← fresh ty
      let c1 := { ctx with locals := { name := n, slot := x, ty, mutable := false } :: ctx.locals }
      let (inner, c2) ← elabOneGo c1 rest
      return (Expr.chooseFirst k x es inner, c2)
    | some b =>
      elabOneChoice ctx b rest
    | none =>
      let (r, c1) ← elabStmt ctx cl none
      let e ← inferable r
      let (inner, c2) ← elabOneGo c1 rest
      return (.seq e inner, c2)

partial def elabOneChoice (ctx : Ctx) (b : Choice.Binding) (rest : List SExpr) : EM (Expr × Ctx) := do
  let p := b.pos
  let n := b.name
  let (pre, ty, es, _) ← match b.branchy with
    | some i => elabBranchAlts ctx p i b.ty b.place
    | none => do let (ty, es) ← elabAlts ctx p b; pure (none, ty, es, false)
  checkNewLocal ctx p n
  let k ← fresh .int
  let x ← fresh ty
  let c1 := { ctx with locals := { name := n, slot := x, ty, mutable := false } :: ctx.locals }
  let (inner, c2) ← elabOneGo c1 rest
  let code := Expr.chooseFirst k x es inner
  return ((pre.map (Expr.seq · code)).getD code, c2)

/-- A call of a recursive function with several values that its consumer
    takes lazily (#246), `$loop(F, params, clauses, r := tail)`, its
    parameters bound by the consumer's clauses before it, to its
    arguments. It runs as a loop over a stack of items, each `(k, F's
    parameters and the names its clauses and conditions bind)`: the
    alternative to run, or -1 to run the clauses and pick the branch of its
    last `if` first (when the clauses fail, the call has no values; what its
    arguments did stays, as for a call computed eagerly). A step pops one
    and runs one alternative. A value is the step's, for the consumer to
    compute; a call of `F` evaluates its arguments and pushes the item that
    starts it. The item that resumes at the next alternative of the choice,
    if any, is pushed below that one (with the names as the arguments left
    them), or once the consumer took or rejected the value (as the consumer
    left them): so the values come in the Verse Calculus's order, depth
    first. The stack is a list of cells (`$lazycell`), so a step costs the
    same however deep the stack is. -/
partial def elabLoopGen (ctx : Ctx) (p : Pos) (lp : List SExpr) : EM LoopGen := do
  let [.ident _ g, .block _ ps, .block _ cls, .decl _ _ (some rsty) _ tail] := lp
    | eerr p "internal: a $loop marker (#246)"
  -- (a strongly connected group's, #283)
  if let .app _ (.ident _ "$group") (tail0 :: members) false := tail then
    let names := g :: members.filterMap fun
      | .app _ (.ident _ "$member") (.ident _ h :: _) false => some h
      | _ => none
    let generic := names.any fun h => ((ctx.sig? h).map (!·.tparams.isEmpty)).getD false
    let pure := names.all fun h => ((ctx.sig? h).map (·.fx.isEmpty)).getD false
    if !generic || !pure then
      return ← elabLoopGenGroupWith elabE elabSeq ctx p g ps cls rsty tail0 members
    return ← tryCatch (elabLoopGenGroupWith elabE elabSeq ctx p g ps cls rsty tail0 members) fun _ => do
      -- Polymorphic recursion was already accepted through F$all. Restart
      -- choice lowering for this group, with all eager restrictions intact.
      noteNeeds { eager := [g] }
      let sp ← fresh .int
      let has ← fresh .logic
      return { init := .lit .void, step := .lit .void, sp, has, value := .prim .fail [],
               after := .lit .void, vty := ← resolveTy ctx.types p rsty, itemCode := .lit .void, argSet := none }
  -- (#283) one whose code after a choice point reaches another: its
  -- continuation members are the group machine's, with it alone in it
  if Choice.hasContinuation tail then
    return ← elabLoopGenGroupWith elabE elabSeq ctx p g ps cls rsty tail []
  let vd : Expr := .lit .void
  -- (the parameters, bound by the consumer's clauses: the loop has slots
  -- of its own for them, so that the call, run again by a loop of its
  -- consumer's, starts from its arguments, not from what its last run left)
  let args ← ps.mapM fun
    | .ident q n => match ctx.lookup n with
      | some l => pure l
      | none => eerr q s!"internal: parameter {n} of a $loop (#246)"
    | e => eerr e.pos "internal: a $loop parameter (#246)"
  let pls ← args.mapM fun l => do return { l with slot := ← fresh l.ty }
  -- (the result type: the signature's, at the type arguments the
  -- arguments give, for a generic one, #235)
  let rty ← match ctx.sig? g with
    | some sig =>
      if sig.tparams.isEmpty then resolveTy ctx.types p rsty else
      match (sig.params.zip args).foldlM (fun σ (pt, l) => Ty.matchArg ctx.types σ pt l.ty) [] with
      | some σ =>
        if let some (v, _) := sig.tparams.find? fun (v, _) => (σ.lookup v).isNone then
          eerr p s!"{g}'s type parameter {v} is not determined by its arguments' types here (#235)"
        pure (sig.ret.subst σ)
      | none => eerr p s!"internal: the arguments of {g} (#235)"
    | none => resolveTy ctx.types p rsty
  let lctx : Ctx := { ctx with locals := pls.reverse ++ ctx.locals }
  let newOf (c : Ctx) : List Local := c.locals.take (c.locals.length - lctx.locals.length)
  -- (the clauses, then each branch's conditions)
  let (rc, cc) ← elabSeq { lctx with canFail := true, inTaking := true } cls none
  let k ← fresh .int
  let code ← elabLoopTailWith elabSeq cc tail k 0
  let armCode := code.arms
  -- (every name to save in an item: the parameters, then the others)
  let mut tls : List Local := pls
  for l in (newOf cc ++ armCode.toList.flatMap fun (ca, _) => newOf ca).reverse do
    if !tls.any (·.slot == l.slot) then tls := tls ++ [l]
  -- (#283) the return frames of the alternatives that are calls with code
  -- after them, and the continuation they are pushed on, the last name
  -- each item keeps
  let frames ← loopFramesWith elabE elabSeq rty armCode.toList
  let lives := frames.map fun f => f.lives.map (·.ty)
  let kl? : Option Local ← if frames.isEmpty then pure none else do
    let kTy := frameContTy lives
    pure (some { name := "$K", slot := ← fresh kTy, ty := kTy, mutable := false })
  tls := tls ++ kl?.toList
  let tupTy : Ty := .tup (.int :: tls.map (·.ty))
  let cellTy : Ty := .struct "$lazycell" [tupTy]
  let cfs := ctx.types.fields "$lazycell" [tupTy]
  let (some (itemF, _), some (nextF, _)) := (fieldIndex cfs "$LItem", fieldIndex cfs "$LNext")
    | eerr p "internal: the stack cells of a $loop (#246)"
  let w ← fresh (.opt cellTy)
  let cell ← fresh cellTy
  let sp ← fresh .int
  let it ← fresh tupTy
  let has ← fresh .logic
  let nx ← fresh .int
  let item (kE : Expr) (vals : List Expr) : Expr := .prim .mkTup (kE :: vals)
  let cur : List Expr := tls.map (Expr.local ·.slot)
  let push (e : Expr) : Expr :=
    .seq (.assign cell (.heap (.new (ctx.types.tagOf "$lazycell")) [e, .local w]))
      (.seq (.assign w (.prim .mkSome [.local cell]))
        (.seq (.assign sp (p2 .add (.local sp) (.lit (.int 1)))) vd))
  -- (the branch an item takes: the first alternative of it)
  let total := code.next
  let starts : List Nat := (armCode.toList.foldl (fun (acc, n) (_, as) => (acc ++ [n], n + as.length)) ([], 0)).1
  let select := code.select
  -- (each alternative's code, numbered across the branches)
  let mut alts : Array Expr := #[]
  let mut values : Array (Nat × Expr) := #[]
  let mut itemCode : Expr := .seq rc.e code.itemCode
  let mut argSet : Option Pos := none
  let mut fi : Nat := 0
  for ((ca, as), start) in armCode.toList.zip starts do
    for (a, j) in as.zipIdx do
      let i := start + j
      let actx : Ctx := { ca with canFail := true, inTaking := true }
      let next? : Option Nat := if j + 1 < as.length then some (i + 1) else none
      let cont : Expr := match next? with
        | some n => push (item (.lit (.int (n : Nat))) cur)
        | none => vd
      -- (a call with code after it: its return frame, pushed with it, #283)
      let fr? : Option LoopFrame := frames[fi]?
      let frameLives : List Local := (fr?.map LoopFrame.lives).getD []
      let (a, kE) : SExpr × Option Expr := match a, kl? with
        | .app _ (.ident _ "$then") (c :: _) false, some kl =>
          (c, some (framePush ctx lives fi (frameLives.map (Expr.local ·.slot)) (.local kl.slot)))
        | a, _ => (a, none)
      -- (its prefix, if any: before the arguments, in whose context they are)
      let pre? : Option Expr := if kE.isSome then fr?.bind (·.pre) else none
      let actx : Ctx := match pre?, fr? with
        | some _, some f => { f.ctx with canFail := true, inTaking := true }
        | _, _ => actx
      if kE.isSome then fi := fi + 1
      match a with
      | .app q (.ident _ "$rec") args' false =>
        if argSet.isNone then
          argSet := args'.findSome? fun a' =>
            if Choice.anyE (fun | .set .. => true | _ => false) a' then some a'.pos else none
        let ts ← pls.mapM fun l => fresh l.ty
        let assigns ← elabLoopArgsWith elabE actx q g args' pls ts
        let assigns := match pre? with | some e => Expr.seq e assigns | none => assigns
        if argSet.isNone && pre?.isSome then argSet := fr?.bind (·.preSet)
        itemCode := .seq itemCode assigns
        -- (the item that resumes after the call, with the names as its
        -- arguments left them, below the one that starts it; when an
        -- argument fails, only the first)
        let vals := ts.map Expr.local ++ cur.drop pls.length
        let start := item (.lit (.int (-1))) (match kE with | some e => vals.dropLast ++ [e] | none => vals)
        alts := alts.push (.ite assigns (.seq cont (push start)) cont)
      | _ =>
        let r ← elabE actx a (some rty)
        values := values.push (i, ← coerce a.pos r rty)
        let nextK : Int := match next? with | some n => (n : Int) | none => -1
        alts := alts.push (.seq (.assign nx (.lit (.int nextK))) (.seq (.assign has (.lit (.logic true))) vd))
  let dispatch : Expr := (alts.toList.zipIdx).foldr (fun (a, i) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) a acc) vd
  let unpack : Expr := (tls.zipIdx).foldr (fun (l, j) acc =>
    .seq (.assign l.slot (.prim (.tupGet (j + 1)) [.local it])) acc) vd
  -- (the call's item: its parameters from the consumer's slots, its
  -- other names as they are)
  let init : Expr := .seq (.assign w (.lit .none)) (.seq (.assign sp (.lit (.int 0)))
    (push (item (.lit (.int (-1))) (args.map (Expr.local ·.slot) ++ cur.drop pls.length))))
  let init : Expr := match kl? with
    | some kl => .seq (.assign kl.slot (.lit .none)) init
    | none => init
  let step : Expr := Expr.seq (.assign sp (p2 .sub (.local sp) (.lit (.int 1))))
    (.seq (.ite (.assign cell (.prim .query [.local w]))
        (.seq (.assign it (.heap (.get itemF) [.local cell])) (.seq (.assign w (.heap (.get nextF) [.local cell])) vd)) vd)
    (.seq (.assign k (.prim (.tupGet 0) [.local it]))
    (.seq unpack
    (.seq (.assign has (.lit (.logic false)))
    (.seq (.ite (p2 .eq (.local k) (.lit (.int (-1))))
        (.ite (.seq rc.e select) vd (.seq (.assign k (.lit (.int (total : Nat)))) vd)) vd)
      dispatch)))))
  -- (the value of the alternative the step came to, which it left in `k`)
  let value : Expr := values.toList.foldr (fun (i, e) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) e acc) (.prim .fail [])
  -- (#283) given to the frames of the item's continuation
  let value ← match kl? with
    | some kl => frameApplyWith elabE ctx p frames rty (.local kl.slot) value
    | none => pure value
  let after : Expr := .ite (p2 .ge (.local nx) (.lit (.int 0))) (push (item (.local nx) cur)) vd
  return { init, step, sp, has, value, after, vty := rty, itemCode, argSet,
           frames := frames.map (fun f => (f.hole, f.lives.map (·.name), f.code)), kTy := kl?.map (·.ty) }

/-- Bind a selected spawn's defaults in the caller, then spawn an adapter
    whose result is the static declaration's result (task types are invariant). -/
partial def elabSpawnBound (ctx : Ctx) (p : Pos) (fname adapter : String)
    (args : List SExpr) : EM R := do
  let some s := ctx.sig? fname | eerr p s!"internal: no spawn signature for {fname}"
  let .struct task [ret] := ctx.retTy | eerr p "internal: no spawn factory result"
  if task != ctx.types.concurrencyName "task" then eerr p "internal: no spawn factory task identity"
  let before := (← get).pendingSuspendingCasts
  let packed ← elabGenericCallWith elabE { ctx with suspends := true } p s args none (packArgs := true)
  let isS (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.suspends
  let skip (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.name == "$spawnMark"
  if before != (← get).pendingSuspendingCasts ||
      Suspend.countSusp isS (fun _ => false) false skip packed.e > 0 then
    eerr p "the arguments of a spawned call cannot suspend (#156)"
  noteFx p s.fx (some fname)
  let .tup ts := packed.ty | eerr p "internal: no packed spawn arguments"
  let receiver ← elabE ctx args[0]! none
  let .struct cls _ := receiver.ty | eerr p "internal: no concrete spawn receiver"
  let params := receiver.ty :: ts.drop 1
  let tps := Ty.mergeParamBounds ((ret :: params).flatMap Ty.paramsC)
  let selfTps := ((ctx.types.sparams.lookup cls).getD []).map (·.1)
  let adapter := s!"{adapter}_{(reprStr params ++ reprStr ret).hash}"
  if (ctx.sig? adapter).isNone then
    let npos := s.params.length - s.named.length
    let forwarded := s.pnames.zipIdx.map fun (n, i) =>
      let value := SExpr.ident p n
      if i < npos then value else .decl p s!"?{(s.named[i - npos]!).1}" none false value
    let lift : Choice.FirstLift := {
      key := s!"defaults:spawnBody:{adapter}", pos := p, name := adapter,
      params := (s.pnames.zip params).zipIdx.map fun ((n, t), i) =>
        { name := n, ty := t.toSTy, typeValue := s.typeValues.contains i },
      tparams := tps.map fun (n, c) =>
        { pos := p, name := n, constraint := if c then "comparable" else "type" },
      specs := (if s.fx.isEmpty then ["computes"] else s.fx) ++ ["suspends"] ++ selfTps.map ("$selfTp:" ++ ·),
      ret := ret.toSTy, body := .app p (.ident p "$spawnResult") [.app p (.ident p fname) forwarded false] false,
      binds := [], sets := [], args := [] }
    noteNeeds { loops := [lift] }
    return ⟨.lit .void, ctx.retTy⟩
  let slot ← fresh packed.ty
  let name := s!"$spawnArgs{slot}"
  let cctx := { ctx with locals := { name, slot, ty := packed.ty, mutable := false } :: ctx.locals }
  let values := args[0]! :: (ts.drop 1).zipIdx.map (fun (_, i) => SExpr.app p (.ident p name) [.int p ((i + 1) : Int)] false)
  let spawned ← elabSpawn cctx p (.app p (.ident p adapter) values false)
  return ⟨.seq (.assign slot packed.e) spawned.e, spawned.ty⟩

/-- A caller-side factory for one implementation and one static declaration.
    All supplied values were evaluated before dispatch; omitted defaults are
    bound in the implementation's own type and declaration scope. -/
partial def elabSpawnDispatch (ctx : Ctx) (p : Pos) (cls fname declared : String)
    (args : List SExpr) (exp : Option Ty) : EM R := do
  let some s := ctx.sig? fname | eerr p s!"internal: no spawn signature for {fname}"
  let some root := ctx.sig? declared | eerr p s!"internal: no static spawn signature for {declared}"
  let impl := (fname.splitOn ".").headD ""
  let owner := (declared.splitOn ".").headD ""
  let cps := (ctx.types.sparams.lookup cls).getD []
  let ips := (ctx.types.sparams.lookup impl).getD []
  let rps := (ctx.types.sparams.lookup owner).getD []
  let clsArgs := cps.map fun (n, c) => Ty.param n c
  let own := (s.tparams.drop ips.length).zipIdx.map fun ((_, c), i) => (s!"$spawnOwn{i}", c)
  let ownArgs := own.map fun (n, c) => Ty.param n c
  let isigma := (ips.map (·.1)).zip (ctx.types.upArgs cls clsArgs impl) ++
    ((s.tparams.drop ips.length).map (·.1)).zip ownArgs
  let rsigma := (rps.map (·.1)).zip (ctx.types.upArgs cls clsArgs owner) ++
    ((root.tparams.drop rps.length).map (·.1)).zip ownArgs
  let ret := root.ret.subst rsigma
  let fullParams := Ty.struct cls clsArgs :: (s.params.drop 1).map (·.subst isigma)
  let npos := s.params.length - s.named.length
  let namedArgs := args.filterMap fun
    | .decl q n _ _ rhs => if n.startsWith "?" then some (q, (n.drop 1).toString, rhs) else none
    | _ => none
  for ((q, n, _), i) in namedArgs.zipIdx do
    if (namedArgs.take i).any (·.2.1 == n) then eerr q s!"?{n} is given twice"
  let named := namedArgs.map fun (_, n, rhs) => (n, rhs)
  let positional := args.filter fun | .decl _ n .. => !n.startsWith "?" | _ => true
  let given := List.range npos ++ (s.named.zipIdx.filterMap fun ((n, _), j) =>
    if named.any (·.1 == n) then some (npos + j) else none)
  let flags : Nat := (if ctx.inRepeat then 1 else 0) + (if ctx.inDefer then 2 else 0) +
    (if ctx.inDefaultCheck then 4 else 0)
  let key := s!"defaults:spawn:{cls}:{fname}:{declared}:{reprStr given}:{reprStr ctx.defaults}:{flags}"
  let name := s!"{cls}.$dispatchDefaultsSpawn{key.hash}"
  let actual := given.filterMap fun i => if i < npos then positional[i]? else
    (s.named[i - npos]?).bind fun (n, _) => named.lookup n
  if (ctx.sig? name).isSome then return ← elabApp ctx p (.ident p name) actual false exp
  let types := given.map fun i => fullParams[i]!
  let used := (ret :: types).flatMap Ty.params
  let tps := (cps ++ own).filter fun (n, _) => used.contains n
  let forwarded := given.map fun i =>
    let value := SExpr.ident p s.pnames[i]!
    if i < npos then value else .decl p s!"?{(s.named[i - npos]!).1}" none false value
  let adapter := s!"{cls}.$spawnBody{key.hash}"
  let stack := ctx.defaults.map fun (f, n) => SExpr.tuple p [.str p [.text f], .str p [.text n]]
  let lift : Choice.FirstLift := {
    key, pos := p, name,
    params := given.map fun i => { name := s.pnames[i]!, ty := fullParams[i]!.toSTy, typeValue := s.typeValues.contains i },
    tparams := tps.map fun (n, c) =>
      { pos := p, name := n, constraint := if c then "comparable" else "type" },
    specs := ["transacts"] ++ cps.map (fun (n, _) => "$selfTp:" ++ n),
    ret := (Ty.struct (ctx.types.concurrencyName "task") [ret]).toSTy,
    body := .app p (.ident p "$defaultContext")
      [.block p stack, .int p (flags : Int), .app p (.ident p "$spawnBound")
        (.ident p fname :: .ident p adapter :: forwarded) false] false,
    binds := [], sets := [], args := [] }
  noteNeeds { loops := [lift] }
  noteFx p s.fx (some fname)
  return ⟨.prim .userErr [], exp.getD (.struct (ctx.types.concurrencyName "task") [ret])⟩

/-- Supply only the already-evaluated arguments to a selected implementation.
    Omitted defaults run in a forwarding helper, after dispatch has refined
    or opened the receiver's types. The helper's default stack preserves
    recursive-default checks across generated function boundaries. -/
partial def elabDefaultDispatch (ctx : Ctx) (p : Pos) (fname : String)
    (args : List SExpr) (bracket : Bool) (exp : Option Ty) : EM R := do
  let some s := ctx.sig? fname | eerr p s!"internal: no signature for {fname}"
  let npos := s.params.length - s.named.length
  let namedArgs := args.filterMap fun
    | .decl q n _ _ rhs => if n.startsWith "?" then some (q, (n.drop 1).toString, rhs) else none
    | _ => none
  for ((q, n, _), i) in namedArgs.zipIdx do
    if (namedArgs.take i).any (·.2.1 == n) then eerr q s!"?{n} is given twice"
  let named := namedArgs.map fun (_, n, rhs) => (n, rhs)
  let omitted := s.named.filter fun (n, _) => !named.any (·.1 == n)
  if omitted.isEmpty then return ← elabApp ctx p (.ident p fname) args bracket exp
  for (n, d) in omitted do
    if d.isNone then eerr p s!"{fname} needs the argument ?{n}, which has no default"
    if ctx.defaults.contains (fname, s!"?{n}") then
      eerr p s!"the default of ?{n} of {fname} uses itself (a call of {fname} that omits ?{n})"
  let positional := args.filter fun | .decl _ n .. => !n.startsWith "?" | _ => true
  let given := (List.range npos) ++ (s.named.zipIdx.filterMap fun ((n, _), j) =>
    if named.any (·.1 == n) then some (npos + j) else none)
  let flags : Nat := (if ctx.inRepeat then 1 else 0) + (if ctx.inDefer then 2 else 0) +
    (if ctx.inDefaultCheck then 4 else 0)
  let key := s!"defaults:{fname}:{reprStr given}:{reprStr ctx.defaults}:{flags}"
  let name := s!"{fname}$dispatchDefaults{key.hash}"
  let actual := given.filterMap fun i => if i < npos then positional[i]? else
    (s.named[i - npos]?).bind fun (n, _) => named.lookup n
  if (ctx.sig? name).isSome then
    return ← elabApp ctx p (.ident p name) actual bracket exp
  let types := given.map fun i => s.params[i]!
  let used := (s.ret :: types).flatMap Ty.params
  let tps := s.tparams.filter fun (n, _) => used.contains n
  let params : List SParam := given.map fun i =>
    { name := s.pnames[i]!, ty := s.params[i]!.toSTy, typeValue := s.typeValues.contains i }
  let forwarded := given.map fun i =>
    let v := SExpr.ident p s.pnames[i]!
    if i < npos then v else SExpr.decl p s!"?{(s.named[i - npos]!).1}" none false v
  let stack := ctx.defaults.map fun (f, n) => SExpr.tuple p [.str p [.text f], .str p [.text n]]
  let body := SExpr.app p (.ident p "$defaultContext")
    [.block p stack, .int p (flags : Int), .app p (.ident p fname) forwarded bracket] false
  let lift : Choice.FirstLift := {
    key, pos := p, name, params,
    tparams := tps.map fun (n, cmp) =>
      { pos := p, name := n, constraint := if cmp then "comparable" else "type" },
    specs := ["transacts"] ++ (if s.decides then ["decides"] else []) ++
      (if s.suspends then ["suspends"] else []) ++ s.selfTps.map ("$selfTp:" ++ ·),
    ret := s.ret.toSTy, body, binds := [], sets := [], args := [] }
  noteNeeds { loops := [lift] }
  noteFx p s.fx (some fname)
  let recv ← elabE ctx positional[0]! none
  -- This round only discovers the helper; it returns before Core checking.
  return ⟨.call s.idx (recv.e :: List.replicate (s.params.length - 1 + s.ndicts) (.lit .void)),
    exp.getD s.ret⟩

/-- `e.m`: `.Length` of an array or string, or a field of a struct. -/
partial def elabMember (ctx : Ctx) (p : Pos) (r : R) (m : String) (exp : Option Ty := none) : EM R := do
  let r ← elabBoundReceiver ctx p r m
  ctx.noteFamily p r.ty m
  match r.ty, m with
  | .arr _, "Length" | .map _ _, "Length" => return ⟨.prim .len [← inferable r], .int⟩
  | .struct sn targs, f =>
    match fieldIndex (ctx.types.fields sn targs) f with
    | some (k, t) =>
      if ctx.types.isRefClass sn then
        -- a reference: the field of its object (#34), at the same position in
        -- every class below a class (inherited fields come first), but maybe
        -- not below an interface: then one test of the object's class each
        let ds := ctx.types.concreteBelow sn
        let pos := ds.map fun d => ((fieldIndex (ctx.types.fields d []) f).map (·.1)).getD k
        if ctx.types.isVarField sn f then noteFx p ["reads"]
        -- (where every class below has it, so does every placeholder below,
        -- even when that is not `k`: an interface listed after another,
        -- #157; and with one type in all of them, #205)
        let env := ctx.types
        let p0 := pos.headD k
        let tyOK := env.fieldTyAgrees sn targs f
        -- (not through views, whose reference has no type arguments of the
        -- object's to read the field at: each class's getter, #351)
        if tyOK && pos.all (· == p0) && !env.viewed.contains sn then return ⟨.heap (.get p0) [r.e], t⟩
        if let some d := ds.find? fun d => !env.sameCore d sn && (env.fieldAcc.idxOf? (d, f)).isNone then
          if !tyOK then
            eerr p s!"field '{f}' of {sn} has another type in {d}, which takes it from another interface, and {d} has type parameters that {sn} does not have: reading it through {sn} is not supported yet (#205)"
          eerr p s!"field '{f}' of {sn} sits at different places in the classes below it, and {d} has type parameters that {sn} does not have: reading it is not supported yet (#53, #157)"
        let x ← fresh r.ty
        let mut acc : Expr := .prim .userErr []   -- no class: unreachable
        let mut refined := false
        -- (#351: through views, only the classes whose view and pins can
        -- give the reference's type arguments, as a method's dispatch
        -- tests; the read is typed even when none can)
        let viewedSn := env.viewed.contains sn
        if viewedSn then refined := true
        for (d, kd) in (ds.zip pos).reverse do
          if viewedSn && (env.viewArgs? sn d (env.coreArgs sn targs) (rigid := false)).isNone then continue
          match env.fieldAcc.idxOf? (d, f) with
          | some i =>
            -- (a class that fixes the type arguments: its getter, under the
            -- refinement, #157)
            acc := .ite (.heap (.isTag [env.tagOf d]) [.local x]) (.call (env.fieldAccBase + 2 * i) [.local x]) acc
            refined := true
          | none =>
            let yd ← fresh (.struct d (env.argsAt sn targs d))
            acc := .ite (.assign yd (.heap (.isTag [env.tagOf d]) [.local x])) (.heap (.get kd) [.local yd]) acc
        if refined then
          -- (checked against the field's type, as the refined calls need one)
          let y ← fresh t
          return ⟨.seq (.assign x r.e) (.assign y acc), t⟩
        return ⟨.seq (.assign x r.e) acc, t⟩
      if ctx.types.classes.contains sn then
        -- a class: the field of whichever option is set (inherited fields come
        -- first, so it has the same position in all of them)
        let ds := ctx.types.concreteBelow sn
        let x ← fresh r.ty
        let mut acc : Expr := .prim .userErr []   -- no option set: unreachable
        for (d, j) in (ds.zip (List.range ds.length)).reverse do
          let dargs := if d == sn then targs else []
          -- the field's position in `d` (the same in all the classes below a
          -- class, but not below an interface)
          let kd := ((fieldIndex (ctx.types.fields d dargs) f).map (·.1)).getD k
          let td ← fresh (classRepTy ctx.types d dargs)
          acc := .ite (.assign td (.prim .query [.prim (.tupGet j) [.local x]])) (.prim (.tupGet kd) [.local td]) acc
        let y ← fresh t
        return ⟨.seq (.assign x r.e) (.assign y acc), t⟩
      return ⟨.prim (.tupGet k) [r.e], t⟩
    | none =>
      if ctx.types.classes.contains sn then
        if f.startsWith "(" then
          eerr p s!"X.{f}, a qualified method, cannot be used as a value: call it with X.{f}(…) (#210)"
        -- (a method that a class below overloads is renamed, #106: one
        -- overload visible here is still a value; more are overloaded)
        let visibleOv := ((ctx.types.methodOverloads.lookup f).getD []).filter (ctx.hasMethod sn ·)
        if visibleOv.length > 1 then
          eerr p s!"'{f}' is an overloaded method of {sn}: an overloaded method cannot be used as a value (Book of Verse ch. 6)"
        let hasValue := (ctx.types.supers sn).any fun x => ctx.types.classes.contains s!"{x}${f}$fn"
        let genericMethod (m : String) : Bool :=
          match ctx.methodDecl? sn m with
          | some owner => (ctx.sig? s!"{owner}.{m}").any fun sg => sg.named.isEmpty &&
              sg.tparams.length > ((ctx.types.sparams.lookup owner).getD []).length
          | none => false
        if ctx.hasMethod sn f || (visibleOv.length == 1 && (hasValue || genericMethod visibleOv.head!)) then
          -- a method as a value (#210): an object of the value class of the
          -- nearest class that declares or overrides it (#219: an override
          -- may narrow the result), holding the receiver, of its type, or
          -- of a class further up whose type is the one expected
          let env := ctx.types
          -- (one implementation per class below, as a call needs, #70; of
          -- the overload visible here, as a class below renamed it, #106)
          let fv := if ctx.hasMethod sn f then f else visibleOv.headD f
          let roots := ctx.rootsOf sn fv
          if let some root := roots.head? then
            for d in env.concreteBelow sn do
              for o in roots do
                if ctx.implFor? d o fv != ctx.implFor? d root fv then
                  eerr p s!"{d} implements {f} separately for {root} and {o}, so the value {f} would not say which: call it as X.({root}:){f}(…) or X.({o}:){f}(…)"
          let typeOf (x : String) : Ty :=
            let cls := s!"{x}${f}$fn"
            let i := (env.info cls).ifaces.headD ""
            let σ := (((env.sparams.lookup cls).getD []).map (·.1)).zip (env.argsAt sn targs x)
            .struct i (((env.iargs.lookup (cls, i)).getD []).map (Ty.subst σ))
          let candidates := (env.supers sn).filter fun x => env.classes.contains s!"{x}${f}$fn"
          -- Fix the captured receiver before inferring an adapter from
          -- the expected function type. Tuple expansion can replace even
          -- a receiver parameter with components; `$self` pins them all.
          let methodTps (x : String) := ((env.sparams.lookup s!"{x}${f}$fn").getD []).drop
            ((env.sparams.lookup x).getD []).length
          if let some target@(.struct shape _) := exp then
            if let some (k, _) := FnValues.parseName shape then
              for x in candidates do
                for cls in [s!"{x}${f}$fn", s!"{x}${f}$fnPack", s!"{x}${f}$fnUnpack{k}"] do
                  if !env.classes.contains cls then continue
                  let some (_, selfTy, _) := (env.fields cls []).find? (·.1 == "$self") | continue
                  let receiver := Ty.struct x (env.argsAt sn targs x)
                  let some fixed := selfTy.matchArg env [] receiver | continue
                  if !(selfTy.subst fixed).eqv receiver then continue
                  let some args := fnClassArgs env cls target fixed | continue
                  let tv ← fresh r.ty
                  let nm := s!"$recv{tv}"
                  let ctx' := { ctx with locals := { name := nm, slot := tv, ty := r.ty, mutable := false } :: ctx.locals }
                  let rv ← elabConstruct ctx' p cls [] [.decl p "$self" none false (.ident p nm)]
                    (some (.struct cls args))
                  return ⟨.seq (.assign tv r.e) (← coerce p rv target), target⟩
          if genericMethod fv || candidates.any (fun x => !(methodTps x).isEmpty) then
            eerr p s!"'{f}' is a generic method of {sn}: a function type determining all its method type arguments and satisfying its bounds must be expected (#209)"
          -- (#231) wanted at a closed function type that no value class of
          -- it gives but that it fits by variance: a class made for that type,
          -- `{x}${f}$fn${k}` (the nearest class's, without type parameters),
          -- holding the receiver; asked for the first time (a placeholder,
          -- and the program is elaborated again with the class made)
          if let some t@(.struct tm tts) := exp then
            if (FnValues.parseName tm).isSome && (tts.all fun u => u.params.isEmpty) &&
                !(candidates.any fun x => typeOf x == t) then
              if let some x0 := candidates.head? then
                if ((env.sparams.lookup s!"{x0}${f}$fn").getD []).isEmpty then
                  let variantTy (c : String) : Ty :=
                    let i := (env.info c).ifaces.headD ""
                    .struct i ((env.iargs.lookup (c, i)).getD [])
                  match env.classes.find? (fun c => c.startsWith s!"{x0}${f}$fn$" && variantTy c == t) with
                  | some vc =>
                    let tv ← fresh r.ty
                    let nm := s!"$recv{tv}"
                    let ctx' := { ctx with locals := { name := nm, slot := tv, ty := r.ty, mutable := false } :: ctx.locals }
                    let rv ← elabConstruct ctx' p vc [] [.decl p "$self" none false (.ident p nm)] (some (.struct vc []))
                    return ⟨.seq (.assign tv r.e) (← coerce p rv t), t⟩
                  | none =>
                    let key := s!".{x0}${f}"
                    if !env.requests.fns.contains (key, t) && fnTyFits env (typeOf x0) t then
                      noteNeeds { fns := [(key, t)] }
                      return ⟨.seq r.e (.prim .userErr []), t⟩
          -- A generic receiver fixes its method's signature too. Requested
          -- adapters retain its witnesses and ordinary call conversions.
          if let some target@(.struct shape _) := exp then
            if (FnValues.parseName shape).isSome then
              for x in candidates do
                if !(methodTps x).isEmpty then continue
                let receiver := Ty.struct x (env.argsAt sn targs x)
                let some (req, args) ← methodVarianceRequest ctx p x f receiver (typeOf x) target | continue
                if let some i := env.requests.methods.findIdx? (·.key == req.key) then
                  let cls := req.className i
                  let tv ← fresh r.ty
                  let nm := s!"$recv{tv}"
                  let ctx' := { ctx with locals := { name := nm, slot := tv, ty := r.ty, mutable := false } :: ctx.locals }
                  let rv ← elabConstruct ctx' p cls [] [.decl p "$self" none false (.ident p nm)]
                    (some (.struct cls args))
                  return ⟨.seq (.assign tv r.e) (← coerce p rv target), target⟩
                noteNeeds { methods := [req] }
                return ⟨.seq r.e (.prim .userErr []), target⟩
          let some x := (candidates.find? fun x => exp == some (typeOf x)).orElse fun _ => candidates.head?
            | -- (#283) a family's stub has none: refused as `Choice.methodFns`
              -- refuses it, before the round that knows the use's family
              match (ctx.methodDecl? sn fv).filter (env.familyStubs.contains s!"{·}.{fv}") with
              | some owner => eerr p s!"{owner.replace "::" "."}.{f} has several values, so it cannot be used as a function value (#235, #283)"
              | none => eerr p s!"'{f}' is a method of {sn} that cannot be used as a value: call it with {f}(…) (a method with named parameters is not a value, #210)"
          let cls := s!"{x}${f}$fn"
          let xargs := env.argsAt sn targs x
          let t ← fresh r.ty
          let nm := s!"$recv{t}"
          let ctx' := { ctx with locals := { name := nm, slot := t, ty := r.ty, mutable := false } :: ctx.locals }
          let rv ← elabConstruct ctx' p cls [] [.decl p "$self" none false (.ident p nm)] (some (.struct cls xargs))
          let own := typeOf x
          return ⟨.seq (.assign t r.e) (← coerce p rv own), own⟩
        if visibleOv.length == 1 then
          eerr p s!"'{f}' is a method of {sn} that cannot be used as a value: call it with {f}(…) (a method with named parameters is not a value, #210)"
        eerr p s!"class {sn} has no field '{f}'"
      eerr p s!"struct {sn} has no field '{f}'"
  | t, m => eerr p s!"{t.show} has no member '{m}'"

/-- A default's declaration scope, actual home-class arguments and cycle
    check, shared by ordinary and choice-lifted construction operands. -/
partial def elabFieldDefault (ctx : Ctx) (p : Pos) (name : String) (tas : List Ty)
    (f : String) (t : Ty) (d : SExpr) : EM Expr := do
  let home := (ctx.types.defaultHome.lookup (name, f)).getD name
  let hσ := (((ctx.types.sparams.lookup home).getD []).map (·.1)).zip (ctx.types.argsAt name tas home)
  let dctx := { ctx with locals := [], selfClass := none, types := { ctx.types with tvars := hσ } }
  if dctx.defaults.contains (name, f) then
    eerr p s!"the default of field '{f}' of {name} depends on itself"
  if f.startsWith SubtypeEvidence.fieldPrefix && !ctx.types.isVarField name f then
    if let (.app _ (.ident _ "$subtypeWitness") [.construct _ "$subtypeEvidence" [base, derived] []] false,
        some bound) := (d, SubtypeEvidence.boundOf? t) then
      let declared ← resolveTy dctx.types p (.app SubtypeEvidence.family [base, derived])
      if declared != t then eerr p "internal: a receiver proof default has the wrong type"
      if ctx.inDefaultCheck && ctx.types.boundSubtype bound.derived bound.base then
        return .prim .userErr []
      let locals := ctx.evidenceTypes
      let some plan := SubtypeEvidence.find? ctx.types locals bound
        | eerr p s!"type {bound.derived.show} does not satisfy subtype({bound.base.show}) in construction of {name}"
      return ← fxAt p (do coerce p (← elabSubtypeValueWith elabE ctx p plan bound) t)
  fxAt p (do coerce p (← elabE { dctx with defaults := (name, f) :: dctx.defaults } d (some t)) t)

/-- `name{F := e, …}` or `name(t₁, …){F := e, …}`: the struct's fields in
    declaration order; omitted fields take their default values. The type
    arguments of a parametric struct are written, or are those of the
    expected type. -/
partial def elabConstruct (ctx : Ctx) (p : Pos) (name : String) (targs : List STy) (args : List SExpr)
    (exp : Option Ty) : EM R := do
  let result ← elabConstructionValue ctx p name targs args exp
  if let some fx := ctx.types.constructionFx[name]? then
    noteFx p fx (some s!"constructs {name} (declared construction budget)")
  return result

partial def elabConstructionValue (ctx : Ctx) (p : Pos) (name : String) (targs : List STy) (args : List SExpr)
    (exp : Option Ty) : EM R := do
  if (ctx.types.structs.lookup name).isNone then eerr p s!"unknown struct '{name}'"
  let ty ← match targs, exp with
    | [], some (.struct n ts) => if n == name then pure (.struct n ts) else resolveTy ctx.types p (.name name)
    | [], _ => resolveTy ctx.types p (.name name)
    | ts, _ => resolveTy ctx.types p (.app name ts)
  let tas := match ty with | .struct _ tas => tas | _ => []
  let fs := ctx.types.fields name tas
  let given ← args.mapM fun a => match a with
    | .decl _ f none false rhs => pure (f, rhs)
    | a => eerr a.pos "a struct field is given as Name := value"
  for (f, _) in given do
    if (fs.find? (·.1 == f)).isNone then eerr p s!"struct {name} has no field '{f}'"
  -- (only the first would be evaluated)
  if let some f := (given.map (·.1)).find? (fun f => (given.filter (·.1 == f)).length > 1) then
    eerr p s!"field '{f}' of {name} is given twice"
  let es ← fs.mapM fun (f, t, dflt) => do
    match given.lookup f, dflt with
    | some rhs, _ => coerce p (← elabE ctx rhs (some t)) t
    | none, some d =>
      elabFieldDefault ctx p name tas f t d
    | none, none => eerr p s!"field '{f}' of {name} has no default value and must be given"
  if ctx.types.classes.contains name then
    let i := ctx.types.info name
    if i.isIface then eerr p s!"{name} is an interface: it cannot be constructed"
    if i.isAbstract then eerr p s!"{name} is <abstract>: it cannot be constructed"
    -- a new object (#34); one that can change, or has an identity, allocates
    if ctx.types.isRefClass name then
      if ctx.types.isUnique name || fs.any (fun (f, _, _) => ctx.types.isVarField name f) then
        noteFx p ["allocates"]
      -- then the `block:` clauses of its class chain, from the top
      let chain := ((ctx.types.supers name).filter fun d => !(ctx.types.info d).isIface).reverse
      let blocks := chain.filterMap fun d => (ctx.sig? s!"{d}.$block").map (d, ·)
      if blocks.isEmpty then
        -- a parametric class's object goes through a temporary of its type,
        -- which gives the checker its type arguments (#39)
        -- (and so does a pinned class's, whose pins may be on more type
        -- arguments than the type it is used at, #209)
        if tas.isEmpty && (ctx.types.corePins name).isEmpty then return ⟨.heap (.new (ctx.types.tagOf name)) es, ty⟩
        let x ← fresh ty
        return ⟨.assign x (.heap (.new (ctx.types.tagOf name)) es), ty⟩
      let x ← fresh ty
      let mut calls : List Expr := []
      for (d, s) in blocks do
        noteFx p s.fx (some s!"constructs {name}, whose block: (in {d})")
        if s.tparams.isEmpty then
          calls := calls ++ [.call s.idx [.local x]]
        else
          -- a parametric class's `block:` is generic (#39): called as a
          -- method, on the new object at its type arguments as a `d`
          let self := s!"$new{x}"
          let dty := Ty.struct d (ctx.types.upArgs name tas d)
          let ctx' := { ctx with locals := { name := self, slot := x, ty := dty, mutable := false } :: ctx.locals }
          let rc ← elabApp ctx' p (.ident p s!"{d}.$block") [.ident p self] false none
          calls := calls ++ [rc.e]
      return ⟨.seq (.assign x (.heap (.new (ctx.types.tagOf name)) es)) (calls.foldr .seq (.local x)), ty⟩
    let x ← fresh ty
    return ⟨.assign x (classWrap ctx.types name name (.prim .mkTup es)), ty⟩
  -- A struct's fields may need their expected types (empty arrays/options
  -- and computed defaults). Preserve the resolved instance before a Core
  -- consumer, such as tuple projection, has to infer its operand's type.
  let x ← fresh ty
  return ⟨.assign x (.prim .mkTup es), ty⟩

/-- `map{k₁ => v₁, …}`: entries are evaluated in order; a key given twice
    keeps its last value, at the position of its last occurrence (Book of
    Verse §9.3). -/
partial def elabMapLit (ctx : Ctx) (p : Pos) (entries : List (SExpr × SExpr)) (exp : Option Ty) : EM R := do
  let (kt?, vt?) := match exp with
    | some (.map k v) => (some k, some v)
    | _ => (none, none)
  match entries with
  | [] =>
    match kt?, vt? with
    | some k, some v => return ⟨.lit Value.emptyArray, .map k v⟩
    | _, _ => eerr p "the type of an empty map{} must be given (e.g. M:[string]int = map{})"
  | (k0, v0) :: _ =>
    let rk0 ← elabE ctx k0 kt?
    let rv0 ← elabE ctx v0 vt?
    let kt := kt?.getD rk0.ty
    if !kt.comparable ctx.types then eerr p (notComparable ctx.types kt "a map key")
    let vt0 := vt?.getD rv0.ty
    let mut rs : Array (SExpr × R × SExpr × R) := #[]
    for (k, v) in entries do
      rs := rs.push (k, ← elabE ctx k (some kt), v, ← elabE ctx v (some vt0))
    -- the values' type: the expected one (or the first's) when every value
    -- converts to it, else their join, as for an array literal (#67)
    let vt ← match ← tryCatch (some <$> rs.toList.mapM fun (_, _, v, rv) => coerce v.pos rv vt0) (fun _ => pure none) with
      | some _ => pure vt0
      | none => rs.toList.foldlM (fun acc (_, _, v, rv) => do
          match joinTy (← get).env acc rv.ty vt? with
          | some j => pure j
          | none => eerr v.pos s!"the values of this map have different types: {acc.show} and {rv.ty.show}") rv0.ty
    let mut steps : Array Expr := #[]
    let mut slots : Array (Nat × Nat) := #[]
    for (k, rk, v, rv) in rs do
      let tk ← fresh kt
      let tv ← fresh vt
      steps := steps.push (.assign tk (← coerce k.pos rk kt))
      steps := steps.push (.assign tv (← coerce v.pos rv vt))
      slots := slots.push (tk, tv)
    let n := slots.size
    let items := (List.range n).map fun i =>
      let (tk, tv) := slots[i]!
      let later := ((List.range n).filter (· > i)).map fun j => Expr.prim .ne [.local tk, .local slots[j]!.1]
      let cond := later.foldr Expr.seq (.lit (.logic true))
      Expr.ite cond (.prim .mkArr [.prim .mkTup [.local tk, .local tv]]) (.lit Value.emptyArray)
    let built := Expr.prim .flatten [.prim .mkArr items]
    return ⟨steps.toList.foldr Expr.seq built, .map kt vt⟩

partial def elabCase (ctx : Ctx) (p : Pos) (scrut : SExpr) (arms : List (Option SExpr × SExpr))
    (exp : Option Ty) : EM R := do
  let rs := widenR ctx.types (← elabE ctx scrut none)
  match rs.ty with
  | .int | .logic | .char | .char32 | .arr .char | .enum _ => pure ()
  | t => eerr p s!"case works on int, logic, char, char32, string and enums, not {t.show}"
  let t ← fresh rs.ty
  let elabArms : List (Option SExpr × SExpr) → EM (Expr × Ty) := fun arms => do
    let mut results : Array (Option Expr × R) := #[]
    for (pat, v) in arms do
      let rv ← elabE ctx v exp
      match pat with
      | none => results := results.push (none, rv)
      | some pe =>
        let rp ← elabE ctx pe (some rs.ty)
        if rp.ty != rs.ty then eerr pe.pos s!"pattern of type {rp.ty.show} for a value of type {rs.ty.show}"
        -- (a pattern is tested in a condition, #156)
        if Suspend.hasSusp (fun f => ctx.sigs.any fun s => s.idx == f && s.suspends) rp.e then
          eerr pe.pos "a case pattern cannot suspend: it is tested as a condition (#156)"
        results := results.push (some rp.e, rv)
    let mut ty : Ty := .never
    for (_, rv) in results do ty ← join p ty rv.ty exp
    let hasDefault := results.any (·.1.isNone)
    -- an enum case that names every enumerator needs no `_` (Book of Verse
    -- §7.6), unless the enum is open: it may gain values (ch. 9)
    let exhaustive := match rs.ty with
      | .enum n =>
        !ctx.types.openEnums.contains n &&
        let k := ((ctx.types.enums.lookup n).getD []).length
        (List.range k).all fun i => results.any fun (pat, _) => match pat with
          | some (.lit (.int j)) => j == i
          | _ => false
      | _ => false
    let mut acc : Expr ← if hasDefault then pure (.lit .void) else
      if exhaustive then pure (.prim .userErr [])   -- unreachable
      else if ctx.canFail then pure (.prim .fail [])
      else match rs.ty with
        | .enum n =>
          if ctx.types.openEnums.contains n then
            eerr p s!"a case on the open enum {n} needs _ (it may gain values), unless failure is allowed (e.g. in a <decides> function)"
          else eerr p "a case without _ is only allowed where failure is (e.g. a <decides> function), or on an enum when every value is named"
        | _ => eerr p "a case without _ is only allowed where failure is (e.g. a <decides> function), or on an enum when every value is named"
    for (pat, rv) in results.reverse do
      let v ← coerce p rv ty
      match pat with
      | none => acc := v
      | some pe => acc := .ite (p2 .eq (.local t) pe) v acc
    return (acc, ty)
  let (body, ty) ← elabArms arms
  return ⟨.seq (.assign t rs.e) body, ty⟩
end

/-- `elabStmt` of the body of a function, a constant or a class's block, from
    `st0`. -/
def elabBody (ctx : Ctx) (body : SExpr) (ret : Option Ty) (st0 : ESt) : Except String ((R × Ctx) × ESt) := do
  -- (a <decides> body of one expression with a cast in it: the block of it,
  -- where a cast that refines takes the rest as its branch, `elabSeqIn`)
  let body := match body with
    | .block .. => body
    | e => if ctx.canFail && !(Refine.castsIn ctx.types.classes.contains e).isEmpty then .block e.pos [e] else e
  (elabStmt ctx body ret).run st0

end OpenVerse.Front
