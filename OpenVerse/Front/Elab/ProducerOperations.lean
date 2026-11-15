import OpenVerse.Front.Elab.Continuations

namespace OpenVerse.Front
open OpenVerse

/-- A synchronous visitor callback forwards to an ordinary shared helper.
    Readonly arguments are captured once; mutable copy-in values come from the
    visitor's current state, and the helper's existing packet supplies copy-outs.
    This retains the helper's source-exit, witness and borrowed-frame protocol. -/
def producerCallbackOf (ctx : Ctx) (p : Pos) (family : String) (frameTypes : List Ty)
    (helper : Choice.FirstLift) (yieldTy resultTy : Ty) (first outcome : Bool) :
    Except String (Choice.FirstLift × SExpr × SExpr × SExpr) := do
  let sets ← helper.sets.mapM fun n => match ctx.lookup n with
    | some l => pure l
    | none => throw s!"internal: missing producer capture {n}"
  let runtimeSets := sets.filter (! ·.typeValue)
  let metadataSets := sets.filter (·.typeValue)
  let stateTy := Ty.tup (runtimeSets.map (·.ty))
  let metadataTy := Ty.tup (metadataSets.map (·.ty))
  let key := "producerCallback" ++ family ++ helper.key ++ s!"{first}{outcome}" ++
    forStageCaptureKey ctx [yieldTy, resultTy] sets
  let name := s!"$producerCallback{key.hash}"
  let params := helper.params.drop 1
  let args := helper.args.drop 1
  let stateIndex (parameter : SParam) : Option Nat :=
    (helper.sets.zipIdx.find? fun (n, _) => parameter.name == n ++ "$in").map (·.2)
  let captured := params.zipIdx.filter (fun (parameter, _) => (stateIndex parameter).isNone)
  let fieldName (parameter : SParam) (i : Nat) :=
    (if parameter.typeValue then "$w." else "") ++ s!"$producerCapture{i}"
  let fields := captured.map fun (parameter, i) =>
    ({ name := fieldName parameter i, ty := parameter.ty } : SField)
  let caps := args.filterMap fun
    | .ident _ n => ctx.lookup n
    | _ => none
  let relations := (SubtypeEvidence.capabilities ctx.types (caps.map fun l =>
    (l.name, if l.typeValue then Ty.void else l.ty))).map (fun plan => plan.bound ctx.types) |>.eraseDups
  let fields := fields ++ SubtypeEvidence.relationFields p name (relations.map fun bound =>
    (bound.base.toSTy, bound.derived.toSTy))
  let ident := SExpr.ident p
  let alias (i : Nat) := s!"$producerArgument{i}"
  let get (value : SExpr) (i : Nat) := SExpr.app p value [.int p (Int.ofNat i)] false
  let init := params.zipIdx.map fun (parameter, i) =>
    let value := match stateIndex parameter with
      | some j =>
        let capture := sets[j]?
        let captureName := capture.map (·.name) |>.getD ""
        let metadata := capture.map (·.typeValue) |>.getD false
        let partition := if metadata then metadataSets else runtimeSets
        let index := (partition.findIdx? (·.name == captureName)).getD 0
        get (ident (if metadata then "$producerMetadata" else "$producerState")) index
      | none => .member p (ident "Self") (fieldName parameter i)
    SExpr.decl p (alias i) (some parameter.ty) false
      (.app p (ident "$forEnvCapture") [value] false)
  let call := SExpr.app p (ident helper.name)
    (ident helper.params.head!.name :: (params.zipIdx.map fun (_, i) => ident (alias i))) true
  let packet := "$producerPacket"
  let copyPartition (locals : List Local) := SExpr.tuple p (locals.map fun capture =>
    let i := (helper.sets.findIdx? (· == capture.name)).getD 0
    get (ident packet) (if first then helper.binds.length + i else i + 1))
  let copied := copyPartition runtimeSets
  let copiedMetadata := copyPartition metadataSets
  let values := if first || helper.sets.isEmpty then ident packet else get (ident packet) 0
  let result := if first then SExpr.tuple p [ident "true", values, copied, copiedMetadata]
    else if outcome then
      .ite p [.decl p "$producerValues" none false (.query p values)]
        (.tuple p [ident "false", ident "$producerValues", copied, copiedMetadata])
        (some (.tuple p [ident "true", .arrayLit p [], copied, copiedMetadata]))
    else .tuple p [ident "false", values, copied, copiedMetadata]
  let body := SExpr.block p (init ++ continuationBind p helper packet call ++ [result])
  let callbackTy := STy.app (family ++ "$consumer") ([yieldTy.toSTy, resultTy.toSTy, stateTy.toSTy, metadataTy.toSTy] ++ frameTypes.map Ty.toSTy)
  let ret := STy.tup [.name "logic", resultTy.toSTy, stateTy.toSTy, metadataTy.toSTy]
  let method := STop.fn p "$take"
    [{ name := helper.params.head!.name, ty := yieldTy.toSTy },
      { name := "$producerState", ty := stateTy.toSTy },
      { name := "$producerMetadata", ty := metadataTy.toSTy, metadataForward := true }]
    [] ("override" :: helper.specs) ret body
  let cls := STop.classDef p name [] helper.tparams [] [callbackTy] false fields [method]
  let storage := (args.zipIdx).filterMap fun (arg, i) => match arg with
    | .ident _ n => (ctx.lookup n).bind fun l => l.storage.map fun s =>
      (alias i, ({ frame := s.frame, name := s.name, args := s.args.map Ty.toSTy } : Choice.ResumeStorage))
    | _ => none
  let resume : Choice.ForResume := {
    name := name ++ ".$take", storage,
    inlineScopes := helper.inlineScopes, liftTag := helper.liftTag,
    inRepeat := true, sourceContext := helper.sourceContext }
  let req : Choice.FirstLift := {
    stageOnly := true, resumes := [resume], key, pos := p, name,
    params := [], specs := ["computes"], ret := .name "void", body := .tuple p [],
    binds := [], sets := [], args := [], extraFns := [cls] }
  let obj := SExpr.construct p name (helper.tparams.map fun tp => .name tp.name)
    (captured.map fun (parameter, i) => .decl p (fieldName parameter i) none false args[i]!)
  let initial := SExpr.tuple p (runtimeSets.map fun l => ident l.name)
  let initialMetadata := SExpr.tuple p (metadataSets.map fun l => ident l.name)
  return (req, obj, initial, initialMetadata)

/-- Resume exactly the environment prepared for this live producer value.
    Its own method retains the existing borrowed-frame and source-exit protocol. -/
def producerForCallbackOf (ctx : Ctx) (p : Pos) (family : String) (frameTypes : List Ty)
    (helper : Choice.FirstLift) (plan : Choice.ForStagePlan)
    (yieldTy readyTy valueTy : Ty) :
    Except String (Choice.FirstLift × SExpr × SExpr × SExpr) := do
  let (req, obj, initial, initialMetadata) ←
    producerCallbackOf ctx p family frameTypes helper yieldTy readyTy false false
  let sets ← helper.sets.mapM fun n => match ctx.lookup n with
    | some l => pure l
    | none => throw s!"internal: missing waiting producer capture {n}"
  let runtimeSets := sets.filter (! ·.typeValue)
  let metadataSets := sets.filter (·.typeValue)
  let stateTy := Ty.tup (runtimeSets.map (·.ty))
  let metadataTy := Ty.tup (metadataSets.map (·.ty))
  let ident := SExpr.ident p
  let get (e : SExpr) (i : Nat) := SExpr.app p e [.int p (Int.ofNat i)] false
  let packet := ident "$resumed"
  let copies (locals : List Local) := SExpr.tuple p (locals.map fun capture =>
    let i := (helper.sets.findIdx? (· == capture.name)).getD 0
    get packet (i + 1))
  let copied := copies runtimeSets
  let copiedMetadata := copies metadataSets
  let values := if helper.sets.isEmpty then packet else get packet 0
  let result := if plan.outcome then
      SExpr.ite p [.decl p "$values" none false (.query p values)]
        (.tuple p [ident "false", ident "$values", copied, copiedMetadata])
        (some (.tuple p [ident "true", .arrayLit p [], copied, copiedMetadata]))
    else .tuple p [ident "false", values, copied, copiedMetadata]
  let call := SExpr.app p (.member p (ident "$environment") plan.method) [] false
  let body := SExpr.ite p [.decl p "$environment" none false (.app p (ident "$ready") [.int p 0] true)]
    (.block p [.decl p "$resumed" none false call, result])
    (some (.app p (ident "Err") [] false))
  let method := STop.fn p "$resume"
    [{ name := "$ready", ty := readyTy.toSTy },
      { name := "$producerState", ty := stateTy.toSTy },
      { name := "$producerMetadata", ty := metadataTy.toSTy, metadataForward := true }]
    [] ("override" :: plan.specs) (.tup [.name "logic", (Ty.arr valueTy).toSTy, stateTy.toSTy, metadataTy.toSTy]) body
  let parent := STy.app (family ++ "$consumer")
    ([yieldTy.toSTy, (Ty.arr valueTy).toSTy, stateTy.toSTy, metadataTy.toSTy, readyTy.toSTy] ++ frameTypes.map Ty.toSTy)
  let extraFns := req.extraFns.map fun
    | .classDef q name cs ts specs _ abstract fields methods =>
      let methods := methods.map fun
        | .fn q "$take" ps ts fx _ (.block bp expressions) =>
          .fn q "$take" ps ts fx readyTy.toSTy (.block bp (expressions.dropLast ++ [ident "$producerPacket"]))
        | other => other
      .classDef q name cs ts specs [parent] abstract fields (methods ++ [method])
    | top => top
  -- Resume forwards the owner without replaying take's copy-in assignments:
  -- the prefix may already have committed writes to that borrowed storage.
  let inheritedStorage := req.resumes.head?.map (·.storage) |>.getD []
  let resume : Choice.ForResume := {
    name := req.name ++ ".$resume", forwarded := inheritedStorage.map (·.2),
    inlineScopes := helper.inlineScopes, liftTag := helper.liftTag,
    inRepeat := true, sourceContext := helper.sourceContext }
  return ({ req with extraFns, resumes := req.resumes ++ [resume] }, obj, initial, initialMetadata)

/-- Consume the complete remaining suffix in each value's live producer scope. -/
def elabProducerForWith
    (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabFor : Ctx → Pos → List SExpr → SExpr → Bool → Bool → Option SExpr → EM R)
    (ctx : Ctx) (p : Pos) (binding : String) (yieldTy : Ty)
    (dictionary receiver : SExpr) (arguments clauses : List SExpr) (body : SExpr)
    (outcome : Bool) : EM R := do
  let dictionaries := dictionary
  let saved ← get
  let slot ← fresh yieldTy
  let bound := { ctx with
    typeOnly := true,
    locals := { name := binding, ty := yieldTy, slot, mutable := false } :: ctx.locals }
  let trial ← elabFor bound p clauses body true (!outcome) none
  let .arr valueTy := trial.ty | eerr p "internal: producer suffix values"
  let waiting := forContWaits ctx saved (← get) [trial.e]
  let effects := (← get).fx
  let sourceSuspends := saved.pendingSourceSuspends != (← get).pendingSourceSuspends || ctx.sourceWaits trial.e
  set saved
  let dictionary := SExpr.app p dictionaries [.int p (if waiting then 2 else 1)] false
  let dictionaryType ← elabE { ctx with typeOnly := true } dictionary none
  let .struct family columns := dictionaryType.ty | eerr p "internal: waiting producer dictionary"
  let frameTypes := columns.drop (arguments.length + 2)
  let allowed := heapFx.filter fun fx => ctx.fnFx.contains fx || effects.any (·.1 == fx)
  let bound := { bound with fnFx := allowed }
  let key := "producerStage" ++ contKey bound p binding (clauses ++ [body])
  let planReq ← match forStagePlanOf bound p key clauses body valueTy outcome [] sourceSuspends
      (suspends := waiting) with
    | .ok request => pure request
    | .error e => eerr p s!"internal: producer stage plan: {e}"
  let some plan := planReq.stagePlan | eerr p "internal: producer stage plan missing"
  let args := plan.tparams.map fun tp =>
    (ctx.types.tvars.lookup tp.name).getD (.param tp.name (tp.constraint == "comparable"))
  let helper ← match forStagePrefixOf bound plan args p clauses body (readyOnly := true) with
    | .ok request => pure request
    | .error e => eerr p s!"internal: producer stage prefix: {e}"
  let helper := { helper with
    sets := plan.copies.map (·.1),
    params := { name := binding, ty := yieldTy.toSTy } :: helper.params.filter (·.name != binding),
    args := .ident p binding :: helper.args.filter (fun e => e != .ident p binding) }
  let readyTy := Ty.arr (.struct plan.base args)
  let (callback, obj, initial, initialMetadata) ← match producerForCallbackOf ctx p family frameTypes helper plan yieldTy readyTy valueTy with
    | .ok result => pure result
    | .error e => eerr p s!"internal: producer stage callback: {e}"
  let mut ready := true
  for req in [planReq, helper, callback] do
    if !(ctx.types.requests.loops.any (·.key == req.key)) then
      askHelper p req
      ready := false
  if waiting then
    modify fun st => { st with
      fx := effects,
      pendingSuspendingCasts := st.pendingSuspendingCasts + 1,
      pendingWaitingCasts := st.pendingWaitingCasts + 1,
      pendingSourceSuspends := st.pendingSourceSuspends + (if sourceSuspends then 1 else 0) }
  if !ready then return ⟨.prim .userErr [], .arr valueTy⟩
  let ident := SExpr.ident p
  let packet := s!"$producerResult{callback.key.hash}"
  let get (i : Nat) := SExpr.app p (ident packet) [.int p (Int.ofNat i)] false
  let call := SExpr.app p (.member p dictionary "$visit") (receiver :: arguments ++ [obj, initial, initialMetadata]) false
  let stateName := packet ++ "$state"
  let runtimeSets := helper.sets.filter fun n => !((ctx.lookup n).map (·.typeValue) |>.getD false)
  let metadataSets := helper.sets.filter fun n => ((ctx.lookup n).map (·.typeValue) |>.getD false)
  let state := ident stateName
  let copyOut := helper.sets.zipIdx.map fun (n, i) => SExpr.set p (ident n) none
    (.app p (ident "$refineCopyOut") [SExpr.app p state [.int p (Int.ofNat i)] false] false)
  let values := SExpr.app p (ident "Concatenate") [get 1] false
  let values := if outcome then
      SExpr.app p (ident "$forOutcomeValues")
        [.ite p [.query p (get 0)] (ident "false") (some (.optionLit p values))] false
    else values
  elabE ctx (.block p ([.decl p packet none false call,
    .decl p stateName none false (.tuple p (helper.sets.map fun n =>
      let metadata := ((ctx.lookup n).map (·.typeValue) |>.getD false)
      let index := ((if metadata then metadataSets else runtimeSets).findIdx? (· == n)).getD 0
      SExpr.app p (get (if metadata then 3 else 2)) [.int p (Int.ofNat index)] false))] ++ copyOut ++ [values])) (some (.arr valueTy))

/-- The same visitor takes the first successful suffix packet. Rejected
    callbacks fail their filter and leave the current capture state unchanged;
    the first admitted callback stops before the next producer alternative. -/
def elabProducerFirstWith
    (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabOneGo : Ctx → List SExpr → EM (Expr × Ctx))
    (ctx : Ctx) (p : Pos) (binding : String) (yieldTy : Ty)
    (dictionary receiver : SExpr) (arguments rest : List SExpr) : EM (Expr × Ctx) := do
  let dictionary := SExpr.app p dictionary [.int p 0] false
  let dictionaryType ← elabE { ctx with typeOnly := true } dictionary none
  let .struct family columns := dictionaryType.ty | eerr p "internal: first producer dictionary"
  let frameTypes := columns.drop (arguments.length + 2)
  let saved ← get
  let slot ← fresh yieldTy
  let bound := { ctx with
    typeOnly := true,
    locals := { name := binding, ty := yieldTy, slot, mutable := false } :: ctx.locals }
  let (_, after) ← elabOneGo bound rest
  let effects := (← get).fx
  let helper ← match contLiftOf ctx after p binding [receiver] rest effects with
    | .ok helper => pure helper
    | .error e => eerr p s!"internal: first producer suffix: {e}"
  set saved
  let resultTy ← resolveTy ctx.types p (helper.joinedRet.getD helper.ret)
  let (callback, obj, initial, initialMetadata) ← match producerCallbackOf ctx p family frameTypes helper yieldTy resultTy true false with
    | .ok v => pure v
    | .error e => eerr p s!"internal: first producer callback: {e}"
  let mut ready := true
  for req in [helper, callback] do
    if !(ctx.types.requests.loops.any (·.key == req.key)) then
      askHelper p req
      ready := false
  let packet := s!"$firstProducerPacket{callback.key.hash}"
  if !ready then
    let slot ← fresh resultTy
    let bound := { ctx with locals := { name := packet, ty := resultTy, slot, mutable := false } :: ctx.locals }
    let (_, after) ← elabOneGo bound (firstUnpack p helper packet)
    return (.prim .userErr [], { after with locals := after.locals.filter (·.name != packet) })
  let ident := SExpr.ident p
  let visitor := packet ++ "$visitor"
  let call := SExpr.app p (.member p dictionary "$first") (receiver :: arguments ++ [obj, initial, initialMetadata]) true
  let first := SExpr.app p (ident visitor) [.int p 0] false
  elabOneGo ctx ([.decl p visitor none false call, .decl p packet (some resultTy.toSTy) false first] ++
    firstUnpack p helper packet)

end OpenVerse.Front
