/- Typed refinement worlds prepared in a filter and resumed after it commits. -/
import OpenVerse.Front.Elab.Continuations

namespace OpenVerse.Front
open OpenVerse

/-- A filterPrefix is searched as one failure context. Each cast gets the whole
    remaining filterPrefix as its branch; only an environment is produced there,
    never the committing consumer body. -/
def refinementPrefixMarker (p : Pos) (clauses : List SExpr) (ready : SExpr) : SExpr :=
  .app p (.ident p "$refinementPrefix") [.block p clauses, ready] false

/-- The annotated view belongs to the caller's world. Ordinary refinement
    substitution changes its arguments in the selected branch, so the
    environment's actual superclass records precisely that world's index. -/
def refinementReadyMarker (p : Pos) (plan : Choice.ForStagePlan) (args : List Ty)
    (copies : List SExpr) (suffix : List SExpr) (body : SExpr) (one : Bool := false) : SExpr :=
  .app p (.ident p (if one then "$refinementReadyOne" else "$refinementReady"))
    [.str p [.text plan.base],
     .decl p "$refinementView" (some (forStageView plan.base (args.map Ty.toSTy))) false (.tuple p []),
     .block p copies, .block p suffix, body] false

/-- Inspect each clause in its own scope; castsIn deliberately treats a
    block as an opaque declaration scope. -/
def hasRefinementClauses (ctx : Ctx) (clauses : List SExpr) : Bool :=
  clauses.any fun clause =>
    (Refine.castClause? clause).any (fun (_, _, target, _) => ctx.types.classes.contains target) ||
    !(Refine.castsIn ctx.types.classes.contains clause).isEmpty

/-- Recovery repairs a refinement/type boundary, never an unrelated source
    restriction such as a cyclic default or a forbidden operation. -/
def refinementRecoveryError (message : String) : Bool :=
  (message.splitOn "the default of field").length == 1 &&
  ((Refine.castRefusal? message).isSome ||
   (message.splitOn "expected ").length > 1 ||
   (message.splitOn "the branches have different types").length > 1 ||
   (message.splitOn "cannot infer the type of this clause's value").length > 1)

/-- Syntax for a preparation transaction. The result type is always the
    opaque Ready view; copy-outs are discharged by its elaborator before
    the consumer can run. -/
def refinementPrepareMarker (ctx : Ctx) (p : Pos) (value : Ty) (outcome rollback : Bool)
    (filterPrefix suffix : List SExpr) (body : SExpr) (forBody : Bool := false) : SExpr :=
  let flags : Nat := (if forBody || ctx.inRepeat then 1 else 0) + (if ctx.inChoice then 2 else 0)
  .app p (.ident p "$refinementPrepare")
    [.decl p "$refinementValue" (some value.toSTy) false (.tuple p []),
     .ident p (if outcome then "true" else "false"),
     .ident p (if rollback then "true" else "false"), .int p (flags : Int),
     .block p filterPrefix, .block p suffix, body] false

/-- Split only at actual source generators. Preparing a later generator
    here would collect environments before earlier consumer bodies ran,
    changing both mutation visibility and the order of effects. -/
def refinementProducerParts (ctx : Ctx) (clauses : List SExpr) :
    Option (List SExpr × List SExpr × List SExpr) := Id.run do
  let isCast (cl : SExpr) := (Refine.castClause? cl).any fun (_, _, target, _) =>
    ctx.types.classes.contains target
  let before := clauses.takeWhile (!isCast ·)
  let remaining := clauses.drop before.length
  if remaining.isEmpty then return none
  let isGenerator : SExpr → Bool
    | .gen .. | .decl _ _ _ false (.range ..) => true
    | cl => Choice.hasChoice [cl] (choiceOrder ctx)
  let filterPrefix := remaining.take 1 ++ (remaining.drop 1).takeWhile (!isGenerator ·)
  if filterPrefix.isEmpty then return none
  return some (before, filterPrefix, remaining.drop filterPrefix.length)

/-- Exit packets returned by a Ready method have the same payload as
    `refineExits`, but the method produces a singleton array of packets.
    The caller still performs the actual return or break after restoring
    mutable outputs. In particular, this never turns a source exit into a
    jump from the preparation failure context. -/
def refinementResumeExits (p : Pos) (exits : Refine.Exits) (outcome : Bool) : Refine.Exits :=
  let packet (statements : List SExpr) : List SExpr :=
    let value := SExpr.arrayLit p [.block p statements]
    [if outcome then .optionLit p (.block p [value]) else value]
  { ret := exits.ret.map fun (binding, statements) => (binding, packet statements),
    brk := exits.brk.map packet }

/-- Carry the existing exit interpretation with the resumed body. These
    declarations are metadata, never source binders or failure clauses. -/
def refinementExitMarker (p : Pos) (exits : Refine.Exits) (body : SExpr) : SExpr :=
  let binding := match exits.ret.bind (·.1) with
    | some (name, ty) => SExpr.decl p name (some ty) false (.tuple p [])
    | none => .tuple p []
  .app p (.ident p "$refinementExits")
    [.ident p (if exits.ret.isSome then "true" else "false"), binding,
     .block p ((exits.ret.map (·.2)).getD []),
     .ident p (if exits.brk.isSome then "true" else "false"),
     .block p (exits.brk.getD []), body] false

/-- Prepare an if's refined filterPrefix without moving its committing body
    into the failure context. Expected typing comes from the ordinary
    caller; source exits use precisely the existing refinement packet. -/
def elabRefinementIfAt (elabE : Ctx → SExpr → Option Ty → EM R)
    (ctx : Ctx) (p : Pos) (clauses : List SExpr) (body : SExpr)
    (otherwise : Option SExpr) (expected : Ty) : EM R := do
  let captures := ctx.capturesOf body
  let written := captures.filter fun captured => captured.mutable &&
    (Refine.findPart (fun
      | .set _ lhs _ _ => Choice.rootName? lhs == some captured.name
      | _ => false) false body).isSome
  let returning := Refine.findPart (fun | .ret .. => true | _ => false) false body
  let breaking := Refine.findPart Refine.isBreak true body
  let escapes := returning.isSome || breaking.isSome
  let mode : ExitVal := if otherwise.isNone || expected == .void then .none
    else if escapes then .opt expected.toSTy else .raw (some expected.toSTy)
  let sourceRet ← match ctx.refineExits.ret with
    | some (some (_, ty), _) => resolveTy ctx.types p ty
    | some (none, _) => pure .void
    | none => match ctx.forReturnSlot.bind ctx.lookup with
      | some { ty := .opt ty, .. } => pure ty
      | _ => pure ctx.retTy
  let sourceRet := if sourceRet == .void then none else some sourceRet.toSTy
  let (thenBody, elseBody, packetType, packetName, after, exits) :=
    refineExits p body otherwise (written.map fun captured => (captured.name, captured.ty.toSTy))
      returning.isSome breaking sourceRet mode
  let some packetType := packetType
    | eerr p "internal: missing expected refinement packet type"
  let body := refinementExitMarker p (refinementResumeExits p exits ctx.canFail) thenBody
  let choose := SExpr.app p (.ident p "$refinementIfPacket")
    [.decl p "$packetType" (some packetType) false (.tuple p []),
     .block p clauses, body, elseBody] false
  elabE ctx (.block p (.decl p packetName (some packetType) false choose :: after)) (some expected)

/-- The Ready method's state parameters are typed in the original world,
    then specialized by the selected environment's superclass arguments. -/
def refinementStagePlanOf (ctx : Ctx) (p : Pos) (key : String)
    (filterPrefix suffix : List SExpr) (body : SExpr) (value : Ty) (outcome : Bool) :
    Except String Choice.FirstLift := do
  let req ← forStagePlanOf ctx p key (filterPrefix ++ suffix) body value outcome []
    (sourceSuspends := ctx.suspends) (suspends := ctx.suspends)
  let some plan := req.stagePlan | throw "internal: refinement stage plan"
  let plan := { plan with
    resumeContext := some (sourceContextOf ctx)
    resumeRollback := ctx.canFail || ctx.inRollback, resumeInputs := true }
  let fields := plan.copies.map fun (n, ty) =>
    ({ name := s!"$refinementCurrent{n}", ty, metadataForward := true } : SParam)
  let definitions := req.extraFns.map fun
    | .classDef q n cs ts fx parents abstract fs methods =>
      .classDef q n cs ts fx parents abstract fs (methods.map fun
        | .fn q n _ ts fx ret body => .fn q n fields ts fx ret body
        | other => other)
    | other => other
  return { req with stagePlan := some plan, extraFns := definitions }

/-- The preparation helper preserves the existing typed frame-owner and
    copy-out protocol. Its result is an opaque, indexed Ready environment;
    opened values never cross this boundary independently. -/
def refinementPrefixOf (ctx : Ctx) (plan : Choice.ForStagePlan) (args : List Ty)
    (p : Pos) (filterPrefix suffix : List SExpr) (body : SExpr) : Except String Choice.FirstLift := do
  let ctx := ctx.choiceCoercionScope
  let qualify := match ctx.selfClass with | some c => selfQualify ctx c | none => id
  let filterPrefix := filterPrefix.map qualify
  let suffix := suffix.map qualify
  let body := qualify body
  let written := ctx.choiceCoercionBody (.block p (filterPrefix ++ suffix ++ [body] ++
    (plan.copies.map (·.1) ++ plan.borrowed).map (SExpr.ident p ·)))
  let caps := ctx.capturesOf written
  let key := "refinementPrepare" ++ plan.key ++ contKey ctx p "$prepare" [written] ++
    forStageCaptureKey ctx args caps
  let name := s!"{plan.base}$prepare{key.hash}"
  let (tps, witnesses, typeArgs) ← contTypes ctx p (caps.map (·.ty)) args written
  let params := caps.map fun l => ({
    name := if l.mutable then l.name ++ "$in" else l.name
    ty := l.ty.toSTy, typeValue := l.typeValue, metadataForward := l.mutable } : SParam)
  let init := caps.filterMap fun l => if !l.mutable then none else some
    (SExpr.decl p l.name (some l.ty.toSTy) true
      (.app p (.ident p "$refineCopyIn") [.ident p (l.name ++ "$in")] false))
  let copies := plan.copies.map fun (n, _) => SExpr.ident p n
  let ready := refinementReadyMarker p plan args copies suffix body
  let code := refinementPrefixMarker p filterPrefix ready
  let value := s!"{name}$ready"
  let view := STy.arr (forStageView plan.base (args.map Ty.toSTy))
  let code := if copies.isEmpty then code else .block p
    [.decl p value (some view) false code, .tuple p (.ident p value :: copies)]
  let σ := (plan.tparams.map (·.name)).zip (args.map Ty.toSTy)
  let ret := if copies.isEmpty then view else .tup (view :: plan.copies.map (fun (_, ty) => ty.substNames σ))
  let storage := caps.filterMap fun l => l.storage.map fun owner =>
    (if l.mutable then l.name ++ "$in" else l.name,
      ({ frame := owner.frame, name := owner.name, args := owner.args.map Ty.toSTy } : Choice.ResumeStorage))
  let info : Choice.ForResume := {
    name, storage
    inlineScopes := ctx.inlineScopes, liftTag := ctx.liftTag,
    sourceContext := sourceContextOf ctx, rollback := ctx.types.signalNoRollback }
  return {
    key, pos := p, name, params := params ++ witnesses, tparams := tps
    specs := plan.specs.filter (· != "suspends") ++ ["decides"], ret,
    sourceContext := sourceContextOf ctx, rollback := ctx.types.signalNoRollback,
    body := ctx.choiceCoercionBody (pruneConstructHints ctx name (.block p (init ++ [code]))),
    binds := [], sets := plan.copies.map (·.1), args := caps.map (fun l => .ident p l.name) ++ typeArgs.map (fun
      | .app q (.ident _ "$witness") [.ident _ n] false =>
        .app q (.ident q "$stageWitness") [.decl q n (some (.name n)) false (.tuple q [])] false
      | value => value),
    resumes := [info] }

/-- Build an indexed environment under the actual selected context. No
    class tag or equality is invented: ordinary source casts established
    this context before this marker was reached. -/
def elabRefinementReady (elabE : Ctx → SExpr → Option Ty → EM R)
    (ctx : Ctx) (p : Pos) (base : String) (view : STy)
    (copies suffix : List SExpr) (body : SExpr) (one : Bool := false) : EM R := do
  let some plan := ctx.types.requests.loops.findSome? (fun r => r.stagePlan.filter (·.base == base))
    | eerr p "internal: missing refinement environment plan"
  let .struct _ args ← resolveTy ctx.types p view
    | eerr p "internal: invalid refinement environment view"
  let c := { ctx with
    forStageArgs := args, forStageFlat := false
    forStageCopies := plan.copies.map (·.1), forStageCopyValues := copies,
    forStageBorrows := plan.borrowed }
  let (request, object, ty) ← match forStageEnvOf c plan p suffix body with
    | .ok value => pure value
    | .error message => eerr p s!"cannot retain this refinement environment: {message}"
  let value ← if ctx.types.requests.loops.any (·.key == request.key) then do
      let fx := (← get).fx
      let r ← elabE c object (some ty)
      let value ← coerce p r ty
      modify fun state => { state with fx }
      pure value
    else do
      askHelper p request
      pure (.prim .userErr [])
  return if one then ⟨value, ty⟩ else ⟨.prim .mkArr [value], .arr ty⟩

/-- Rename live clause values without treating constructor field labels as
    local declarations. A source local still cannot shadow a live clause local. -/
private partial def refinementRenameValues (renames : List (String × String))
    (expression : SExpr) : EM SExpr := do
  match expression with
  | .ident p name => return .ident p ((renames.lookup name).getD name)
  | .construct p name types fields =>
    let fields ← fields.mapM fun
      | .decl q label annotation mutable value => do
        return .decl q label (annotation.map (Choice.renameValueTypes renames)) mutable
          (← refinementRenameValues renames value)
      | value => refinementRenameValues renames value
    return .construct p name (types.map (Choice.renameValueTypes renames)) fields
  | .decl p name annotation mutable value =>
    if (renames.lookup name).isSome then
      eerr p s!"'{name}' is already defined; Verse does not allow shadowing (use set {name} = … for a var)"
    return .decl p name (annotation.map (Choice.renameValueTypes renames)) mutable
      (← refinementRenameValues renames value)
  | .gen p name index source =>
    for name in name :: index.toList do
      if (renames.lookup name).isSome then
        eerr p s!"'{name}' is already defined; Verse does not allow shadowing (use set {name} = … for a var)"
    return .gen p name index (← refinementRenameValues renames source)
  | expression => expression.mapChildrenM (refinementRenameValues renames)

/-- Keep caller-nameable clause locals in live caller slots. Their source
    initializers remain at the original clause; only the compiler's inert
    slot default moves to the enclosing private scope. Bindings become visible
    after their initializer, as they do in ordinary clause elaboration. -/
def refinementOwnedLocals (ctx : Ctx) (p : Pos) (clauses : List SExpr)
    (body : SExpr) : EM (Option SExpr) := do
  let written := SExpr.forE p clauses body
  let assigned := Choice.setsIn written
  let stem := "refinementLocal" ++ contKey ctx p "$locals" [written]
  let mut locals : List (String × String × Ty) := []
  let mut earlier : List String := []
  for clause in clauses do
    if let .decl q name (some annotation) true _ := clause then
      if assigned.contains name then
        checkNewLocal ctx q name
        if earlier.contains name then
          eerr q s!"'{name}' is already defined; Verse does not allow shadowing (use set {name} = … for a var)"
        let saved ← get
        let ty ← tryCatch (some <$> resolveTy ctx.types q annotation) (fun _ => pure none)
        set saved
        if let some ty := ty.filter (!·.hasNever) then
          locals := locals ++ [(name, s!"$refinementLocal{stem.hash}_{name}", ty)]
    earlier := earlier ++ Choice.boundIn [clause]
  if locals.isEmpty then return none
  let mut renames : List (String × String) := []
  let mut rewritten : List SExpr := []
  for clause in clauses do
    match clause with
    | .decl q name _ true value =>
      if let some (_, privateName, _) := locals.find? (fun binding => binding.1 == name) then
        let value ← refinementRenameValues renames value
        rewritten := rewritten ++ [.decl q (privateName ++ "$initialized") none false
          (.block q [.set q (.ident q privateName) none value, .tuple q []])]
        renames := renames ++ [(name, privateName)]
      else rewritten := rewritten ++ [← refinementRenameValues renames clause]
    | clause => rewritten := rewritten ++ [← refinementRenameValues renames clause]
  let body ← refinementRenameValues renames body
  let defaults := locals.map fun (_, name, ty) => SExpr.decl p name (some ty.toSTy) true
    (.app p (.ident p "$refinementSlotDefault")
      [.decl p "$type" (some ty.toSTy) false (.tuple p [])] false)
  return some (.block p (defaults ++ [.forE p rewritten body]))

/-- The same compiler-owned typed cell used by lazy function frames. -/
def refinementCellRequest (p : Pos) : Choice.FirstLift := {
  stageOnly := true, key := "$refinementVarCell", name := "$refinementVarCell", pos := p
  params := [], tparams := [], specs := ["computes"], ret := .name "void", body := .tuple p []
  binds := [], sets := [], args := []
  extraFns := [.classDef p "$varcell" [] [{ pos := p, name := "t", constraint := "type" }]
    [] [] false [{ name := "$VCell", ty := .name "t", isVar := true }] []] }

/-- Plain source generators keep the Book's depth-first search journal. Calls
    with several values deliberately retain their existing producer boundary. -/
def refinementPlainGenerator (ctx : Ctx) : SExpr → Bool
  | .gen .. | .decl _ _ _ false (.range ..) => true
  | clause => (Choice.binding? clause).any fun binding =>
      !binding.composed && binding.branchy.isNone && binding.each.isNone

def refinementChainEligible (ctx : Ctx) (written suffix : List SExpr) : Bool :=
  !suffix.isEmpty && refinementPlainGenerator ctx suffix.head! &&
    !(written.any fun expression => Choice.anyE (fun
      | .app _ (.ident _ name) _ _ => ["$inline", "$each", "$loop", "$dispatch", "$point"].contains name
      | _ => false) expression) &&
    suffix.all (fun clause =>
      !((Choice.binding? clause).isSome || (match clause with | .gen .. | .decl _ _ _ false (.range ..) => true | _ => false)) ||
        refinementPlainGenerator ctx clause)

private structure RefinementChainNode where
  request : Choice.FirstLift
  args : List Ty
  clauses : List SExpr
  body : SExpr

private def RefinementChainNode.plan (node : RefinementChainNode) : Choice.ForStagePlan :=
  node.request.stagePlan.getD default

private def RefinementChainNode.ty (node : RefinementChainNode) : Ty :=
  .struct node.plan.base node.args

private def RefinementChainNode.ready (node : RefinementChainNode) (p : Pos) : SExpr :=
  refinementReadyMarker p node.plan node.args
    (node.plan.copies.map fun (name, _) => .ident p name) node.clauses node.body (one := true)

/-- One typed source/filter/body phase. Source/filter methods never wait;
    only the final body retains the source consumer's suspension and exits. -/
private def refinementChainNodeOf (ctx : Ctx) (p : Pos) (key : String)
    (written : List SExpr) (sourceBody : SExpr) (value : Ty)
    (outcome rollback originalFor consumer : Bool) (clauses : List SExpr) (body : SExpr) :
    Except String RefinementChainNode := do
  let phase := if consumer then ctx else { ctx with
    suspends := false, fnFx := ctx.fnFx.filter (· != "suspends") }
  let request ← refinementStagePlanOf phase p key written [] sourceBody value outcome
  let some plan := request.stagePlan | throw "internal: refinement chain plan"
  let source := { (sourceContextOf ctx) with inRepeat := consumer || ctx.inRepeat }
  let plan := { plan with
    resumeRollback := rollback
    resumeContext := some source
    resumeOriginalFor := originalFor }
  let args := plan.tparams.map fun parameter =>
    (ctx.types.tvars.lookup parameter.name).getD (.param parameter.name (parameter.constraint == "comparable"))
  return { request := { request with stagePlan := some plan }, args, clauses, body }

/-- Preserve the original generator search in the caller. Each source yields
    opaque row owners; each row's filters produce its next world. Only the
    final world's method executes the consumer, outside physical filters. -/
partial def refinementChainOf (ctx : Ctx) (p : Pos) (headClauses suffix : List SExpr)
    (body : SExpr) (value : Ty) (outcome rollback : Bool) : EM (Option (List SExpr × SExpr)) := do
  let rec groups : List SExpr → List (SExpr × List SExpr)
    | [] => []
    | generator :: rest =>
      let filters := rest.takeWhile (!refinementPlainGenerator ctx ·)
      (generator, filters) :: groups (rest.drop filters.length)
  let written := headClauses ++ suffix
  let key := "refinementChain" ++ contKey ctx p "$search" (written ++ [body]) ++ reprStr value
  let final ← match refinementChainNodeOf ctx p (key ++ "body") written body value
      outcome rollback false true [] body with
    | .ok node => pure node
    | .error message => eerr p message
  let mut current := final
  let mut nodes := [final]
  let mut stages : List (RefinementChainNode × RefinementChainNode) := []
  for ((generator, filters), index) in (groups suffix).zipIdx.reverse do
    let filter ← match refinementChainNodeOf ctx p (key ++ s!"filter{index}") written body current.ty
        true true false false [] (refinementPrefixMarker p filters (current.ready p)) with
      | .ok node => pure node
      | .error message => eerr p message
    let source ← match refinementChainNodeOf ctx p (key ++ s!"source{index}") written body filter.ty
        false true true false [generator] (filter.ready p) with
      | .ok node => pure node
      | .error message => eerr p message
    stages := (source, filter) :: stages
    nodes := source :: filter :: nodes
    current := source
  let mut pending := false
  for node in nodes do
    if !ctx.types.requests.loops.any (·.key == node.request.key) then
      askHelper p node.request
      pending := true
  if pending then return none
  let root := current
  let stem := s!"$refinementSearch{p.line}_{p.col}_{ctx.locals.length}"
  let prepare := SExpr.app p (.ident p "$refinementPrepareKnown")
    [.str p [.text root.plan.base], .block p headClauses, .block p root.clauses, root.body] false
  let first (name : String) (array : SExpr) := SExpr.block p
    [.decl p (name ++ "$array") none false array,
     .app p (.ident p (name ++ "$array")) [.int p 0] true]
  let resume (world : String) (filter : Bool := false) :=
    SExpr.app p (.ident p (if filter then "$refinementFilterResume" else "$refinementResume"))
      [.arrayLit p [.ident p world]] false
  let mut world := stem ++ "$world0"
  let mut clauses := [SExpr.decl p world none false (first world prepare)]
  for (_, index) in stages.zipIdx do
    let row := stem ++ s!"$row{index}"
    let next := stem ++ s!"$world{index+1}"
    clauses := clauses ++ [.gen p row none (resume world),
      .decl p next none false (first next (resume row true))]
    world := next
  return some (clauses, forStageBodyAs body (resume world))

end OpenVerse.Front
