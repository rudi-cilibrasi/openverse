/- A contiguous expression-handler stage; fallthrough preserves source pattern order. -/
import OpenVerse.Front.Elab.Control

namespace OpenVerse.Front
open OpenVerse

/-- The refusal of a choice, or of a call of a function with several values,
    left where it is (`what` names it; `several`, followed by "must be …",
    says that it has several values; `issue` is where they came in): where a
    failure context takes its values (`inTaking`), lifting did not reach it,
    from `liftWhy` when that is known; elsewhere, nothing takes them. -/
def refuseSeveral (ctx : Ctx) (p : Pos) (what several issue : String) : EM R := do
  if ctx.inTaking then
    if ctx.liftWhy != "" then
      eerr p s!"{what} cannot be lifted from {ctx.liftWhy}, for now (#283)"
    eerr p (s!"{what} cannot be lifted from here, for now ({issue}): not from the body of a loop, " ++
      "which takes no choice")
  -- (#283) a `<suspends>` function has one value: a call of one with
  -- several would be in a failure context, which cannot suspend (#156)
  let why := if ctx.suspends then
      "; a <suspends> function cannot have several values, as a call of it would be in a failure context, which cannot suspend (#156)"
    else ""
  eerr p (s!"{several} must be in a failure context that takes them: " ++
    s!"an if condition, a for's clauses, first\{…}, option\{…}, logic\{…}, not, or the left of or ({issue}){why}")

/-- `refuseSeveral` for a call of `f`, a function with several values (#235). -/
def refuseCall (ctx : Ctx) (p : Pos) (f : String) : EM R :=
  let shown := Choice.shownFnName f
  refuseSeveral ctx p s!"a call of {shown}, which has several values," s!"{shown} has several values, so a call of it" "#235"

set_option maxHeartbeats 800000 in
partial def elabExprMarkersWith
    (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabRefineExit : Ctx → Pos → List SExpr → List SExpr → EM R)
    (elabConc : Ctx → Pos → Bool → List SExpr → Option Ty → (isRush : optParam Bool false) → EM R)
    (elabSpawn : Ctx → Pos → SExpr → EM R)
    (elabBranch : Ctx → Pos → SExpr → EM R)
    (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (elabFor : Ctx → Pos → List SExpr → SExpr → (prepared : optParam Bool false) → (firstDecides : optParam Bool false) → (failure : optParam (Option SExpr) none) → EM R)
    (elabOneClauses : Ctx → List SExpr → EM (R × Ctx))
    (elabFirstGo : Ctx → List SExpr → EM (Expr × Ctx))
    (next : Ctx → SExpr → Option Ty → EM R)
    (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  match se with
  | .app _ (.ident _ "$mapKeySources") [.block _ keys, value] false =>
    let result ← elabE ctx value exp
    let keyTy := match result.ty with | .map k _ | .weakMap k _ => some k | _ => none
    let saved ← get
    let checked ← tryCatch (do
      for key in keys do
        set saved
        let r ← elabE { ctx with typeOnly := true } key keyTy
        checkMapKeyCanFail ctx key.pos r.e
      pure (Except.ok ())) (fun err => pure (Except.error err))
    set saved
    match checked with
    | .ok _ => return result
    | .error err => throw err
  | .app _ (.ident _ "$producerAnchorStart") [_] false
    | .app _ (.ident _ "$producerAnchorEnd") [_] false
    | .app _ (.ident _ "$producerFrameStart") [] false
    | .app _ (.ident _ "$producerFrameEnd") [] false => return ⟨.lit .void, .void⟩
  | .app _ (.ident _ "$nofail") [e] false =>
    elabE { ctx with canFail := false, inRollback := ctx.inRollback || ctx.canFail, inBlock := true } e exp
  | .app p (.ident _ "$defer") _ _ => eerr p "defer: is a statement: it has no value"
  | .app _ (.ident _ "$deferExits") [.block _ ds, e] false =>
    -- (#283) the `defer:`s of a scope whose clauses are lifted, which run
    -- after its value (`Choice.deferLast`), pending for the exits in `e`,
    -- as a `defer:` is for the rest of its scope (`elabSeqIn`)
    elabE (ds.foldl (fun c d => match d with
      | .app _ (.ident _ "$defer") [body] false => c.withDefer body
      | _ => c) ctx) e exp
  | .app _ (.ident _ "$noteFails") [.str _ [.text key], e] false => do
    -- (#283) a `for` in a recursive group's code that consumes a call, kept
    -- for checking until its function of its own is made
    -- (`Choice.nestFns`): whether it can fail, as its function then must
    let r ← elabE ctx e exp
    if r.e.mayFail ctx.sigProg then noteNeeds { nested := [(key ++ "$fails", .name "logic")] }
    return r
  | .app p (.ident _ "$sync") arms false => elabConc ctx p true arms exp
  | .app p (.ident _ "$race") arms false => elabConc ctx p false arms exp
  | .app p (.ident _ "$rush") arms false => elabConc ctx p false arms exp true
  | .app p (.ident _ "$spawn") [body] false => elabSpawn ctx p body
  | .app p (.ident _ "$branch") [body] false => elabBranch ctx p body
  | .app p (.ident _ "$refineBreak") [] false =>
    match ctx.refineExits.brk with
    | some pack =>
      if ctx.inDefer then eerr p "break cannot leave a defer: block"
      elabRefineExit ctx p [] pack
    | none => elabE ctx (.brk p) exp
  | .app _ (.ident _ "$witness") [.ident _ n] false =>
    -- (a value of type parameter `n`, as the hidden argument of a generic
    -- call for it: the type argument of a lifted branch (#243) that only its
    -- written types mention)
    let t := (ctx.types.tvars.lookup n).getD (.param n false)
    return ⟨← witness ctx.types ctx.dictBase ctx.dictVars t, t⟩
  | .app p (.ident _ "$stageWitness") [.decl _ _ (some ty) _ _] false => do
    let ty ← resolveTy ctx.types p ty
    return ⟨← witness ctx.types ctx.dictBase ctx.dictVars ty, ty⟩
  | .app p (.ident _ "$fxOf") [.ident _ f] false =>
    -- (an inlined call of a function with several values: its declared
    -- effects, as at a call, #235)
    if let some s := ctx.sig? f then noteFx p s.fx (some s!"calls {Choice.shownFnName f}")
    return ⟨.lit .void, .void⟩
  -- (a continuation's body, #335: clauses lifted already, failing where their
  -- first filter does, then the values)
  | .app p (.ident _ "$forFirst") [.block _ clauses, body] false => elabFor ctx p clauses body (prepared := true) (firstDecides := true)
  | .app _ (.ident _ "$forEnvCapture") [value] false => do
    let fx := (← get).fx
    let r ← elabE ctx value exp
    modify fun st => { st with fx }
    return r
  | .app p (.ident _ "$forStageFlatten") [value] false => do
    let r ← elabE ctx value none
    match r.ty with
    | .arr (.arr t) => return ⟨← flattenValues r, .arr t⟩
    | .opt (.arr (.arr t)) =>
      let result ← fresh r.ty
      let slot ← fresh (.arr (.arr t))
      return ⟨.seq (.assign result r.e) (.ite (.assign slot (.prim .query [.local result]))
        (.prim .mkSome [.prim .flatten [.local slot]]) (.lit .none)), .opt (.arr t)⟩
    | _ => eerr p "internal: staged flatten values"
  | .app p (.ident _ "$refinementIfPacket")
      [.decl _ _ (some packetType) _ _, .block _ clauses, body, otherwise] false => do
    let ty ← resolveTy ctx.types p packetType
    let name := s!"$refinementIf{p.line}_{p.col}_{ctx.locals.length}"
    let ready := name ++ "$ready"
    let values := name ++ "$values"
    -- The caller supplies the existing refineExits packet body and
    -- dispatches that packet afterwards. Only preparation is tested by
    -- this conditional; failure in the resumed committing body cannot
    -- accidentally select the source else branch.
    let prepare := refinementPrepareMarker ctx p ty ctx.canFail (ctx.canFail || ctx.inRollback)
      clauses [] body
    let resume := SExpr.app p (.ident p "$refinementResume") [.ident p ready] false
    let result := name ++ "$packet"
    let get := SExpr.app p (.ident p values) [.int p 0] true
    let consumer := SExpr.block p
      [.decl p values none false resume,
       .ite p [.decl p result none false get] (.ident p result)
         (some (.app p (.ident p "Err") [] false))]
    elabE ctx (.ite p [.decl p ready none false prepare] consumer (some otherwise)) exp
  | .app p (.ident _ "$refinementFirst")
      [.decl _ _ (some resultType) _ _, .block _ clauses, value] false => do
    if !ctx.canFail then
      eerr p "first{…} with a choice can fail, but it is not in a failure context (#208)"
    let ty ← resolveTy ctx.types p resultType
    let name := s!"$refinementFirst{p.line}_{p.col}_{ctx.locals.length}"
    let ready := name ++ "$ready"
    -- Resume the source value after its clauses, as the ordinary first
    -- handler does. Its continuation remains in the same search: a failed
    -- value tries the next alternative without repeating earlier operands.
    let prepare := refinementPrepareMarker ctx p ty true (ctx.canFail || ctx.inRollback)
      clauses [] value
    let resume := SExpr.app p (.ident p "$refinementResume") [.ident p ready] false
    let values := name ++ "$values"
    elabE ctx (.block p
      [.decl p ready none false prepare,
       .decl p values none false resume,
       .app p (.ident p values) [.int p 0] true]) exp
  | .app p (.ident _ "$refinementBody") [.str _ [.text base], body] false => do
    let some plan := ctx.types.requests.loops.findSome? (fun request => request.stagePlan.filter (·.base == base))
      | eerr p "internal: missing refinement consumer scope"
    let some source := plan.resumeContext | eerr p "internal: missing source consumer scope"
    elabE { ctx with inRepeat := source.inRepeat, inChoice := source.inChoice } body exp
  | .app _ (.ident _ "$refinementExits")
      [.ident _ returns, binding, .block _ returnPacket,
       .ident _ breaks, .block _ breakPacket, body] false => do
    let binding := match binding with
      | .decl _ name (some ty) _ _ => some (name, ty)
      | _ => none
    let exits : Refine.Exits := {
      ret := if returns == "true" then some (binding, returnPacket) else none,
      brk := if breaks == "true" then some breakPacket else none }
    elabE { ctx with refineExits := exits } body exp
  | .app p (.ident _ "$refinementPrefix") [.block _ clauses, ready] false => do
    let ctx := { ctx with refinementTransportActive := true }
    match clauses with
    | [] => elabE ctx ready exp
    | cl :: rest =>
      let tail := refinementPrefixMarker p rest ready
      if let some (_, _, target, _) := Refine.castClause? cl then
        if ctx.types.classes.contains target then
          -- Keeping all later filterPrefix work in the then branch avoids
          -- exporting a narrowed snapshot and trying to recover its world.
          return ← elabE ctx (.ite cl.pos [cl, .query cl.pos (.ident cl.pos "true")]
            tail (some (Refine.noValue cl.pos))) exp
      -- A cast in a computed bound must precede the remaining prefix,
      -- retaining its selected world rather than replaying its owner.
      if let some position := (Refine.castsIn ctx.types.classes.contains cl).head? then
        let lifted ← liftCastClause elabE ctx [] position cl
        return ← elabE ctx (refinementPrefixMarker p (lifted ++ rest) ready) exp
      -- The continuation participates in the same search, so a later
      -- failed cast still backtracks through an earlier choice.
      let result := s!"$refinementNext{cl.pos.line}_{cl.pos.col}_{rest.length}"
      elabE ctx (.app p (.ident p "$first")
        [.block p [cl, .decl p result (exp.map Ty.toSTy) false tail, .ident p result]] false) exp
  | .app p (.ident _ "$refinementReady")
      [.str _ [.text base], .decl _ _ (some view) _ _, .block _ copies, .block _ suffix, body] false
  | .app p (.ident _ "$refinementReadyOne")
      [.str _ [.text base], .decl _ _ (some view) _ _, .block _ copies, .block _ suffix, body] false =>
    elabRefinementReady elabE ctx p base view copies suffix body
      (one := match se with | .app _ (.ident _ "$refinementReadyOne") _ _ => true | _ => false)
  | .app p (.ident _ "$refinementSlotDefault")
      [.decl _ _ (some annotation) _ _] false => do
    let ty ← resolveTy ctx.types p annotation
    let params := ((ctx.sig? ctx.frameName).map (·.params)).getD []
    match slotDefault ctx.types ctx.dictBase params [] ty with
    | .ok value => pure ⟨value, ty⟩
    | .error message => eerr p message
  | .app p (.ident _ "$refinementPrepareKnown")
      [.str _ [.text base], .block _ headClauses, .block _ suffix, body] false => do
    let some plan := ctx.types.requests.loops.findSome? (fun request =>
      request.stagePlan.filter (·.base == base)) | eerr p "internal: missing refinement chain source"
    let args := plan.tparams.map fun parameter =>
      (ctx.types.tvars.lookup parameter.name).getD (.param parameter.name (parameter.constraint == "comparable"))
    let helper ← match refinementPrefixOf ctx plan args p headClauses suffix body with
      | .ok helper => pure helper
      | .error message => eerr p message
    if !ctx.types.requests.loops.any (·.key == helper.key) then
      askHelper p helper
      return ⟨.prim .fail [], .arr (.struct plan.base args)⟩
    let call := SExpr.app p (.ident p helper.name) helper.args true
    if plan.copies.isEmpty then return ← elabE ctx call exp
    let packet := base ++ "$prepared"
    let get (index : Nat) := SExpr.app p (.ident p packet) [.int p (index : Int)] false
    let copied := plan.copies.zipIdx.map fun ((name, _), index) =>
      SExpr.set p (.ident p name) none
        (.app p (.ident p "$refineCopyOut") [get (index+1)] false)
    elabE ctx (.block p (.decl p packet none false call :: copied ++ [get 0])) exp
  | .app p (.ident _ "$refinementPrepare")
      [.decl _ _ (some valueType) _ _, .ident _ outcome, .ident _ rollback, .int _ flags,
       .block _ filterPrefix, .block _ suffix, body] false => do
    let value ← resolveTy ctx.types p valueType
    let key := "refinementWorld" ++ contKey ctx p "$ready" (filterPrefix ++ suffix ++ [body]) ++
      reprStr (value, outcome, rollback, flags)
    let request ← match refinementStagePlanOf ctx p key filterPrefix suffix body value (outcome == "true") with
      | .ok request => pure request
      | .error message => eerr p s!"cannot prepare this refinement world: {message}"
    let some plan := request.stagePlan | eerr p "internal: refinement plan"
    let source := { (sourceContextOf ctx) with
      inRepeat := flags.toNat % 2 == 1, inChoice := (flags.toNat / 2) % 2 == 1 }
    let plan := { plan with resumeRollback := rollback == "true", resumeContext := some source }
    let request := { request with stagePlan := some plan }
    let args := plan.tparams.map fun tp =>
      (ctx.types.tvars.lookup tp.name).getD (.param tp.name (tp.constraint == "comparable"))
    if !(ctx.types.requests.loops.any (·.key == request.key)) then
      askHelper p request
      return ⟨.prim .fail [], .arr (.struct plan.base args)⟩
    let helper ← match refinementPrefixOf ctx plan args p filterPrefix suffix body with
      | .ok helper => pure helper
      | .error message => eerr p s!"cannot capture this refinement world: {message}"
    if !(ctx.types.requests.loops.any (·.key == helper.key)) then
      askHelper p helper
      return ⟨.prim .fail [], .arr (.struct plan.base args)⟩
    let call := SExpr.app p (.ident p helper.name) helper.args true
    if plan.copies.isEmpty then return ← elabE ctx call exp
    -- Copy-out belongs to the preparation transaction. The opaque Ready
    -- value alone crosses into the committing consumer; evaluate its
    -- preparation exactly once before assigning the mutable outputs.
    let packet := s!"{plan.base}$prepared"
    let get (j : Nat) := SExpr.app p (.ident p packet) [.int p (j : Int)] false
    let assignments := plan.copies.zipIdx.map fun ((name, _), j) =>
      SExpr.set p (.ident p name) none
        (.app p (.ident p "$refineCopyOut") [get (j + 1)] false)
    elabE ctx (.block p (.decl p packet none false call :: assignments ++ [get 0])) exp
  | .app p (.ident _ "$refinementResume") [environments] false
  | .app p (.ident _ "$refinementFilterResume") [environments] false => do
    let ctx := match se with
      | .app _ (.ident _ "$refinementFilterResume") _ _ =>
        { ctx with forOutcomeSlot := none, forExitPacket := none }
      | _ => ctx
    let r ← elabE ctx environments none
    let .arr (.struct base args) := r.ty | eerr p "internal: refinement ready values"
    let known := ctx.types.requests.loops.findSome? (fun r => r.stagePlan.filter (·.base == base))
    if known.isNone then
      -- The plan requested by preparation belongs to the next ordinary
      -- elaboration pass. Keep a typed placeholder in this disposable
      -- pass instead of dispatching an as-yet undeclared method.
      let pending := (← get).loopFirst.findSome? fun use =>
        use.lift.toOption.bind fun request => request.stagePlan.filter (·.base == base)
      let some plan := pending | eerr p "internal: missing refinement resume plan"
      let σ := (plan.tparams.map (·.name)).zip (args.map Ty.toSTy)
      let value ← resolveTy ctx.types p (plan.value.substNames σ)
      return ⟨.prim .userErr [], .arr value⟩
    let some plan := known | eerr p "internal: missing refinement resume plan"
    elabE ctx (.app p (.ident p "$forResumeValues")
      [environments, forStageCopyMetadata p (plan.copies.map (·.1)),
       .block p (plan.borrowed.map (SExpr.ident p ·))] false) exp
  | .app p (.ident _ "$forPrepare") [.str _ [.text base], .decl _ _ (some view) _ _, .block _ copyIds, .block _ borrowIds, .ident _ flat, .block _ clauses, body] false => do
    let some plan := ctx.types.requests.loops.findSome? (fun l => l.stagePlan.filter (·.base == base))
      | eerr p "internal: missing for prepare plan"
    let .struct _ args ← resolveTy ctx.types p view | eerr p "internal: for prepare view"
    let copyNames := forStageCopyNames copyIds
    let borrowNames := borrowIds.filterMap fun | .ident _ n => some n | _ => none
    let req ← match forStagePrefixOf ctx plan args p clauses body (flat == "true") copyNames borrowNames with
      | .ok req => pure req
      | .error why => eerr p s!"cannot prepare this refining for: {why} (#417)"
    if !ctx.types.requests.loops.any (·.key == req.key) then
      askHelper p req
      let ty ← resolveTy ctx.types p req.ret
      return ⟨.prim .userErr [], ty⟩
    elabApp ctx p (.ident p req.name) req.args true exp
  | .app p (.ident _ "$forStage") [.str _ [.text base], .decl _ _ (some view) _ _, .block _ copyIds, .block _ borrowIds, .ident _ root, .ident _ flat, .block _ clauses, body] false => do
    let some plan := (ctx.forStage.filter (·.base == base)).orElse fun _ =>
        ctx.types.requests.loops.findSome? (fun l => l.stagePlan.filter (·.base == base))
      | eerr p "internal: missing for stage plan"
    let .struct _ args ← resolveTy ctx.types p view | eerr p "internal: for stage view"
    let copyNames := forStageCopyNames copyIds
    let borrowNames := borrowIds.filterMap fun | .ident _ n => some n | _ => none
    let outcome := root == "true" && plan.outcome
    let failed : SExpr := if plan.copies.isEmpty then .ident p "false" else
      .tuple p (.ident p "false" :: copyNames.map (SExpr.ident p ·))
    let r ← elabFor { ctx with
      forStage := some plan, forStageArgs := args, forStageFlat := flat == "true", forStageCopies := copyNames, forStageBorrows := borrowNames,
      forExitPacket := if outcome then some failed else ctx.forExitPacket } p clauses body
      (prepared := true) (firstDecides := true)
    if !outcome then return r
    return ⟨.prim .mkSome [r.e], .opt r.ty⟩
  | .app p (.ident _ "$forResumeValues") [envs, .block _ copyIds, .block _ _] false => do
    let copyNames := forStageCopyNames copyIds
    let input ← elabE ctx envs none
    let r ← match input.ty with
      | .opt (.arr _) => forOutcomeValues ctx p input
      | _ => pure input
    let .arr (.struct base _) := r.ty | eerr p "internal: for resume environments"
    let some plan := ctx.types.requests.loops.findSome? (fun l => l.stagePlan.filter (·.base == base))
      | eerr p "internal: missing for resume plan"
    let slot ← fresh r.ty
    let source := s!"{base}$ready"
    let env := source ++ "$env"
    let packet := source ++ "$packet"
    let c := { ctx with forStage := none, locals := { name := source, slot, ty := r.ty, mutable := false } :: ctx.locals }
    let inputs := if plan.resumeInputs then copyNames.map (SExpr.ident p ·) else []
    let call := SExpr.app p (.member p (.ident p env) plan.method) inputs false
    let body := if plan.copies.isEmpty then call else
      let get (j : Nat) := SExpr.app p (.ident p packet) [.int p (j : Int)] false
      SExpr.block p (.decl p packet none false call ::
        (copyNames.zipIdx.map fun (n, j) => .set p (.ident p n) none
          (.app p (.ident p "$refineCopyOut") [get (j + 1)] false)) ++ [get 0])
    let body := if plan.outcome then .app p (.ident p "$forOutcomeValues") [body] false else body
    -- Preparation never executes a real generator: each successful filterPrefix
    -- supplies exactly one environment. Dispatch directly, retaining the
    -- enclosing outcome target across this suspending call.
    let first := SExpr.app p (.ident p source) [.int p 0] true
    let values ← elabE c (.ite p [.decl p env none false first] body
      (some (.app p (.ident p "Err") [] false))) none
    let .arr _ := values.ty | eerr p "internal: for resume values"
    return ⟨.seq (.assign slot r.e) values.e, values.ty⟩
  | .app p (.ident _ "$forFirstOutcome") [.block _ clauses, body, failed] false => do
    let flag ← fresh .logic
    let r ← elabFor { ctx with forOutcomeSlot := some flag, forExitPacket := some failed } p clauses body
      (prepared := true) (firstDecides := true) (failure := some failed)
    let result ← fresh (.opt r.ty)
    return ⟨.seq (.assign flag (.lit (.logic true)))
      (.seq (.assign result (.lit .none))
        (.seq (.loop (.seq (.assign result (.prim .mkSome [r.e])) Expr.brkV))
          (.ite (.prim .query [.local flag]) (.local result) (.lit .none)))), .opt r.ty⟩
  | .app p (.ident _ "$forOutcomeValues") [value] false => do
    forOutcomeValues ctx p (← elabE ctx value none)
  | .app _ (.ident _ "$forReturns") [_, .ident _ mode, body] false =>
    elabE { ctx with canFail := mode == "true" } body exp
  | .app _ (.ident _ "$forReturnBody") [.set _ (.ident _ slot) none _, .ident _ mode, body] false =>
    elabE { ctx with canFail := mode == "true", defers := [], forReturnSlot := some slot } body exp
  | .app _ (.ident _ "$forReturnBody") [.block _ [.set _ (.ident _ slot) none _, _], .ident _ mode, body] false =>
    elabE { ctx with canFail := mode == "true", defers := [], forReturnSlot := some slot } body exp
  -- (#283) a family's stub, `Err()`: a program with a call of it is
  -- refused (`elabProgramCore`)
  | .app p (.ident _ "$familyStub") [] false => elabE ctx (.app p (.ident p "Err") [] false) exp
  -- (#283, `Choice.bifToExcl`) a block as an `if`'s branch binding a name
  -- its condition binds
  | .app _ (.ident _ "$shadows") [.ident q n] false =>
    eerr q s!"'{n}' is already defined; Verse does not allow shadowing (use set {n} = … for a var)"
  | .app p (.ident _ "$inline") (.ident _ f :: _) false => refuseCall ctx p f
  -- (a call of a recursive function with several values, #235)
  | .app p (.ident _ "$each") (.app _ (.ident _ fa) _ _ :: _) false =>
    refuseCall ctx p (if fa.endsWith "$all" then String.ofList (fa.toList.take (fa.length - 4)) else fa)
  -- (a call of a recursive function with several values taken lazily, #246)
  | .app p (.ident _ "$loop") (.ident _ f :: _) false => refuseCall ctx p f
  | .app p (.ident _ "$choice") _ false =>
    refuseSeveral ctx p "a choice (a | b)" "a choice (a | b) has several values, so it" "#208"
  | .app p (.ident _ "$callSingleton") [a] false =>
    -- Elaborate the operand once, then reuse its checked result for either
    -- the whole tuple or its singleton element. Failed conversions must not
    -- discard successful nested elaboration and repeat the operand tree.
    if let some (pt@(.tup [inner])) := exp then
      let r ← if ← argNeedsTypeWith elabE ctx a then
          tryCatch (elabE ctx a (some inner)) (fun _ => elabE ctx a (some pt))
        else tryCatch (elabE ctx a none) fun err => do
          if !(← argumentContextUsefulWith elabE ctx a err) then throw err
          tryCatch (elabE ctx a (some inner)) (fun _ => elabE ctx a (some pt))
      match (coerce a.pos r pt).run (← get) with
      | .ok (e, state) => set state; return ⟨e, pt⟩
      | .error _ =>
        return ⟨.prim .mkTup [← coerce a.pos r inner], pt⟩
    let r ← elabE ctx a none
    match r.ty with
    | .tup [_] | .never => return r
    | _ => return ⟨.prim .mkTup [r.e], .tup [r.ty]⟩
  | .app p (.ident _ "$callArgs") [.ident _ g, .block _ args] false =>
    let some sig := ctx.sig? g | eerr p s!"internal: no signature for {g}'s arguments"
    if let some (.tup types) := exp then
      return ← elabRecursiveArgsWith elabE ctx p sig args types
    elabGenericCallWith elabE ctx p sig args exp (packArgs := true)
  | .app p (.ident _ "$callArgs") [.ident _ g, .block _ args, .block _ types] false =>
    let some sig := ctx.sig? g | eerr p s!"internal: no signature for {g}'s arguments"
    let inst ← types.mapM fun
      | .decl q n (some t) _ _ => do pure (n, ← resolveTy ctx.types q t)
      | _ => eerr p "internal: a recursive call's type instance"
    if let some (.tup types) := exp then
      return ← elabRecursiveArgsWith elabE ctx p sig args types inst
    elabGenericCallWith elabE ctx p sig args exp (packArgs := true) (inst := inst)
  | .app p (.ident _ "$paramDefault") [.ident _ f, .ident _ n, .block _ earlier, d] false =>
    -- (#283) the default of a named parameter an inlined call of a function
    -- with several values omits: in the context a call gives it (the
    -- parameters before it, under their own names; no return; failing only
    -- for a <decides> function)
    let some s := ctx.sig? f | eerr p s!"internal: no signature for {f} (#283)"
    let locals : List Local := earlier.filterMap fun
      | .tuple _ [.ident _ orig, .ident _ t] => (ctx.lookup t).map fun l => { l with name := orig }
      | _ => none
    let key := (s.name, s!"?{n}")
    if ctx.defaults.contains key then
      eerr p s!"the default of ?{n} of {f} uses itself (a call of {f} that omits ?{n})"
    let dctx := { ctx with locals := locals.reverse, selfClass := none, inParamDefault := true,
                           inLoop := false, canFail := ctx.canFail && s.decides,
                           inRollback := ctx.inRollback || ctx.canFail,
                           suspends := ctx.suspends && s.suspends, defaults := key :: ctx.defaults }
    let rd ← fxAt p (elabE dctx d exp)
    if !s.decides && rd.e.mayFail ctx.sigProg then
      eerr p s!"the default of ?{n} of {f} can fail, but {f} is not <decides>"
    return rd
  | .app _ (.ident _ "$noLift") [.str _ [.text why], e] false =>
    -- (#283) a block or construction kept: elaborated as it is, its choice
    -- refused with why
    elabE { ctx with liftWhy := why } e exp
  -- (#283) a lazily taken call's function of its own with return frames:
  -- frame `j` pushed on the continuation `k`, holding the lives' values,
  -- and a value given to the continuation's frames, as the lazy loop does
  | .app p (.ident _ "$framePush") (.int _ j :: k :: lives) false =>
    let rk ← elabE ctx k none
    let some tys := frameLivesOf rk.ty | eerr p "internal: a frame's continuation (#283)"
    let vals ← (lives.zip (tys.getD j.toNat [])).mapM fun (a, t) => do coerce a.pos (← elabE ctx a (some t)) t
    return ⟨framePush ctx tys j.toNat vals rk.e, rk.ty⟩
  | .app p (.ident _ "$frameApply") (k :: leaf :: frames) false =>
    let rk ← elabE ctx k none
    let some tys := frameLivesOf rk.ty | eerr p "internal: a frame's continuation (#283)"
    let rl ← elabE ctx leaf exp
    let rty := exp.getD rl.ty
    let fs ← (frames.zip tys).mapM fun
      | (.app _ (.ident _ "$frame") [.ident _ h, .block _ lives, code] false, ts) =>
        pure ({ hole := h, code, ctx, lives := (lives.zip ts).filterMap fun
          | (.ident _ n, t) => some { name := n, slot := 0, ty := t, mutable := false }
          | _ => none } : LoopFrame)
      | _ => eerr p "internal: a return frame (#283)"
    return ⟨← frameApplyWith elabE ctx p fs rty rk.e (← coerce leaf.pos rl rty), rty⟩
  | .app p (.ident _ "$frameReturn") (k :: leaf :: rest) false =>
    -- (#283) a value `leaf` given to the continuation `k` where a
    -- continuation member's frame is a call of that member's function: the
    -- packet that call gives, or, when no such frame comes, `fin`, which
    -- reads the final value as `leaf`, or, with frames of other types, as a
    -- name of its own at the result type
    let rk ← elabE ctx k none
    let some tys := frameLivesOf rk.ty | eerr p "internal: a frame's continuation (#283)"
    let some vl := (match leaf with | .ident _ n => ctx.lookup n | _ => none)
      | eerr p "internal: a frame's value (#283)"
    let (vfin?, fin, frames) ← match rest with
      | .block _ [.decl _ vfn (some vfsty) _ _] :: fin :: frames => do
        let vty ← resolveTy ctx.types p vfsty
        pure (some ({ name := vfn, slot := ← fresh vty, ty := vty, mutable := false } : Local), fin, frames)
      | fin :: frames => pure (none, fin, frames)
      | [] => eerr p "internal: a frame's continuation (#283)"
    let vty := (vfin?.map (·.ty)).getD vl.ty
    let vf := (vfin?.map (·.slot)).getD vl.slot
    let rf ← elabE { ctx with locals := vfin?.toList ++ ctx.locals } fin exp
    let pty := exp.getD rf.ty
    let pk ← fresh pty
    let done ← fresh .logic
    -- (a frame's types, when not the result type: `$in`, `$out`)
    let tyOf (ds : List SExpr) (n : String) : EM (Option Ty) := do
      match ds.findSome? fun | .decl _ m (some t) _ _ => if m == n then some t else none | _ => none with
      | some t => return some (← resolveTy ctx.types p t)
      | none => return none
    let fs ← (frames.zip tys).mapM fun
      | (.app _ (.ident _ f) (.ident _ h :: .block _ lives :: code :: more) false, ts) => do
        let lives := (lives.zip ts).filterMap fun
          | (.ident _ n, t) => some ({ name := n, slot := 0, ty := t, mutable := false } : Local)
          | _ => none
        let ds := match more with | [.block _ ds] => ds | _ => []
        let (inTy, outTy) := (← tyOf ds "$in", ← tyOf ds "$out")
        if f == "$frameCall" then pure ({ hole := h, code, ctx, lives, member := some 0, inTy, outTy } : LoopFrame)
        else pure { hole := h, code, ctx, lives, inTy, outTy }
      | _ => eerr p "internal: a return frame (#283)"
    let memberArm (j t : Nat) (slotOf : Option Ty → Nat) (kk : Nat) : EM Expr := do
      let some f := fs[j]? | eerr p "internal: a return frame (#283)"
      let ls ← f.lives.mapM fun l => do return { l with slot := ← fresh l.ty }
      let hty := f.inTy.getD vty
      let h ← fresh hty
      let c : Ctx := { ctx with canFail := true, inTaking := true, locals :=
        { name := "$Krest", slot := kk, ty := rk.ty, mutable := false } ::
        { name := f.hole, slot := h, ty := hty, mutable := false } :: ls.reverse ++ ctx.locals }
      let r ← elabE c f.code (some pty)
      let e ← coerce f.code.pos r pty
      let unpack := ls.zipIdx.foldr (fun (l, i) acc => Expr.seq (.assign l.slot (.prim (.tupGet i) [.local t])) acc) (.lit .void)
      return .seq unpack (.seq (.assign h (.local (slotOf f.inTy))) (.seq (.assign pk e)
        (.seq (.assign done (.lit (.logic true))) Expr.brkV)))
    -- (a leaf of another type than the result's, a value going to a
    -- choice's frame, starts in that type's slot)
    let typedLeaf := !(vl.ty == vty)
    let code ← frameApplyWith elabE ctx p fs vty rk.e (.local vl.slot) memberArm
      (fun v => .ite (.prim .query [.local done]) (.local pk) (.seq (.assign vf (.local v)) rf.e))
      (if typedLeaf then some fun slotOf => .assign (slotOf (some vl.ty)) (.local vl.slot) else none)
      (if typedLeaf then [vl.ty] else [])
    return ⟨.seq (.assign done (.lit (.logic false))) code, pty⟩
  | .app p (.ident _ "$copiedOverloads") [.str _ [.text scope], .app q (.ident _ "$firstP") [.block bp items] false] false =>
    let code ← match ctx.specializeCopiedOverloads scope items with
      | .ok code => pure code
      | .error why => eerr p why
    -- These clauses have already been prepared. Re-lifting an untouched
    -- returning callee can change its argument/backtracking order (#653).
    let bound := Choice.boundIn code
    let prepared := (items.zip code).zipIdx.flatMap fun ((before, after), i) =>
      if before == after then [after] else
        Choice.prepare [after] (fun n => choiceValues ctx n || bound.contains n) (choiceField ctx)
          (site := s!"copy{scope.hash}_{i}") (fieldOrder := choiceOrder ctx) (keepBranches := choiceHasCast ctx)
    elabE { ctx with copiedOverloadScope := scope, copiedOverloadSites := prepared.flatMap Choice.copiedOverloadUses }
      (.app q (.ident q "$firstP") [.block bp prepared] false) exp
  | .app p (.ident _ "$firstP") [.block _ items] false =>
    -- (#246) `first{…}` of clauses that are lifted already (a consumer's,
    -- taken into a lazily taken call's function of its own): not again,
    -- which would bind their lifted names a second time
    let (code, c1) ← elabFirstGo { ctx with canFail := true } items.dropLast
    let rv ← elabE { c1 with canFail := ctx.canFail } (items.getLastD (.tuple p [])) exp
    return ⟨.seq code rv.e, rv.ty⟩
  | .app p (.ident _ "$first") [.block bp items] false =>
    if !ctx.refinementTransportActive && hasRefinementClauses ctx items then
      if let some expected := exp.filter (!·.hasNever) then
        let saved ← get
        if !saved.refiningHintProbe then
          return ← tryCatch (elabE { ctx with refinementTransportActive := true } se exp) fun original => do
            if !refinementRecoveryError original then throw original
            set saved
            let request := SExpr.app p (.ident p "$refinementFirst")
              [.decl p "$valueType" (some expected.toSTy) false (.tuple p []),
               .block bp items.dropLast, items.getLastD (.tuple p [])] false
            tryCatch (elabE { ctx with refinementTransportActive := true } request exp) fun _ => do
              set saved
              throw original
    -- `first{…}` and `first(…){…}`: without a choice, a block
    if !Choice.hasChoice items.dropLast (choiceOrder ctx) then return ← elabE ctx (.block bp items) exp
    -- with one (#208): the first success of the clauses, then the value (or
    -- body), which sees their names
    if !ctx.canFail then
      eerr p "first{…} with a choice can fail, but it is not in a failure context (#208)"
    -- (#243, #351) a clause that casts as only a failure context's clause
    -- may: as written, else with the rest of its clauses as one block
    let asWritten := ctx.asWritten
    let ctx := { ctx with asWritten := false }
    let value := items.getLastD (.tuple p [])
    if !asWritten then
      -- The parser's range producer can compile a bound cast locally,
      -- hiding its refinement before the first's following clauses are
      -- typed. Probe those bounds in the context of the preceding clauses;
      -- only a cast that actually needs refinement takes the outer path.
      let clauses := items.dropLast
      let saved ← get
      for (clause, k) in clauses.zipIdx do
        let source := match clause with | .decl _ _ _ _ v => v | e => e
        if let some (lo, hi, _) := Choice.firstRangeBounds? source then
          let casts := Refine.castsIn ctx.types.classes.contains clause
          if !casts.isEmpty then
            let filterPrefix? ← tryCatch (do
              let (_, before) ← elabOneClauses { ctx with canFail := true, typeOnly := true } (clauses.take k)
              pure (some (before, ← get))) (fun _ => pure none)
            set saved
            if let some (before, prefixState) := filterPrefix? then
              for bound in [lo, hi] do
                set prefixState
                let refusal? ← tryCatch (do
                  discard <| elabE { before with canFail := true, inTaking := true, typeOnly := true } bound none
                  pure none) (fun err => pure (Refine.castRefusal? err))
                set saved
                if let some refusal := refusal? then
                  if casts.contains refusal.pos then
                    set prefixState
                    let lifted ← liftCastClause elabE before (Choice.boundIn (clauses.take k)) refusal.pos clause
                    set saved
                    return ← elabE ctx (.app p (.ident p "$first")
                      [.block bp (clauses.take k ++ lifted ++ clauses.drop (k + 1) ++ [value])] false) exp
      if let some r ← withCastClauses elabE elabOneClauses ctx items.dropLast value (fun _ => false) (elabE { ctx with asWritten := true } se exp)
          (fun cs v => elabE ctx (.app p (.ident p "$first") [.block bp (cs ++ [v])] false) exp) then
        return r
    let (rc, c1) ← elabOneClauses ctx items.dropLast
    let rv ← elabE c1 (items.getLastD (.tuple p [])) exp
    return ⟨.seq rc.e rv.e, rv.ty⟩
  | _ => next ctx se exp

end OpenVerse.Front
