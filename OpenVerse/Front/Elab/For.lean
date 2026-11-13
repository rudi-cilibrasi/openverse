/- Elaboration for; public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Continuations

namespace OpenVerse.Front
open OpenVerse
/-- (#283, #331) The type of a choice of an `if`'s branches with no type
    written, from its `$joinOf` (`Choice.joinOf?`): the branches' join, as
    the `if`'s value has, found by elaborating the `if` apart for the type
    only (that code is not kept); for `set L = if …`, at `L`'s type.
    `elabBranchAlts` is the mutual block's, as for `elabForWith`. -/
def joinOfType (elabBranchAlts : Ctx → Pos → SExpr → Option STy → Option SExpr → EM (Option Expr × Ty × List Expr × Bool))
    (ctx : Ctx) (p : Pos) (alts : List SExpr) : EM (Option STy) := do
  let some (i, place) := Choice.joinOf? alts | return none
  let st ← get
  let (_, ty, _, _) ← elabBranchAlts { ctx with canFail := true, inTaking := true, typeOnly := true } p i none place
  restoreConstructProbe ctx st
  return some ty.toSTy

/-- `for`: clauses are generators, bindings and filters; each generator opens
    a nested `forE`, and nested results are flattened (cartesian product,
    leftmost outermost). The clauses are a failure context; the body is not.
    Defined before the mutual block, with the functions of the block it
    calls as arguments (named as they are), so that it is a command of its
    own, with its own heartbeats (#325); `elabFor` in the block passes them. -/
partial def elabForWith (elabAlts : Ctx → Pos → Choice.Binding → EM (Ty × List Expr))
    (elabBranchAlts : Ctx → Pos → SExpr → Option STy → Option SExpr → EM (Option Expr × Ty × List Expr × Bool))
    (elabE : Ctx → SExpr → Option Ty → EM R) (elabInts : Ctx → Pos → List SExpr → EM (List Expr))
    (elabLoopGen : Ctx → Pos → List SExpr → EM LoopGen) (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx))
    (ctx : Ctx) (p : Pos) (clauses : List SExpr) (body : SExpr) (prepared : Bool := false)
    (firstDecides : Bool := false) (failure : Option SExpr := none) : EM R := do
  let stagePlan := ctx.forStage
  let stageArgs := ctx.forStageArgs
  let stageFlat := ctx.forStageFlat
  let stageCopies := ctx.forStageCopies
  let stageBorrows := ctx.forStageBorrows
  let ctx := { ctx with liftWhy := "", forStage := none, forStageArgs := [], forStageFlat := false, forStageCopies := [], forStageBorrows := [] }
  -- (a choice is a generator over its alternatives, #208; clauses lifted
  -- already, `prepared`, are not lifted again)
  let clauses := if prepared then clauses else
    Choice.prepare clauses (choiceValues ctx) (choiceField ctx) (fieldOrder := choiceOrder ctx) (keepExcl := true)
      (keepBranches := choiceHasCast ctx)
  -- (a call of a recursive function with several values, #235: a generator
  -- over the array of its values; at a written type, through a binding)
  let normGens (cs : List SExpr) : List SExpr := cs.flatMap fun c => match Choice.binding? c with
    -- (one taken lazily, #246: the binding stays, a generator of its own)
    | some { each := some (.app _ (.ident _ "$loop") _ false), .. } => [c]
    | some { pos := q, name := n, ty, each := some arr, .. } => Choice.genOver "" q n ty arr
    | _ => [c]
  let clauses := normGens clauses
  -- split into groups: [filters before the first generator], then (generator, filters)…
  let isBranch (c : SExpr) : Bool := (Choice.binding? c).any (·.branchy.isSome)
  let isGen : SExpr → Bool
    | .gen .. => true
    | .decl _ _ none false (.range ..) => true
    | c => !isBranch c && (Choice.binding? c).isSome
  -- (an exclusive choice's binding, #314: no generator, but paths)
  let isExcl : SExpr → Bool
    | .decl _ _ _ false (.app _ (.ident _ "$excl") _ false) => true
    | c => isBranch c
  -- (a composed choice whose alternatives have values or clauses of their
  -- own, #283, or an exclusive one: what a continuation saves copying, #335)
  let isCF (x : SExpr) : Bool := isExcl x || (Choice.binding? x).any (·.composed)
  let pre := clauses.takeWhile (!isGen ·)
  let rest := clauses.dropWhile (!isGen ·)
  let rec groups : List SExpr → List (SExpr × List SExpr)
    | [] => []
    | g :: cs =>
      let fs := cs.takeWhile (!isGen ·)
      (g, fs) :: groups (cs.dropWhile (!isGen ·))
  let gs := groups rest
  -- A failable continuation body returns an explicit outcome. Its first
  -- filter still fails the call, so the caller retains that boundary.
  let bodyFail := (ctx.canFail && !firstDecides) || failure.isSome || forReturnBody? body
  let bodyCtx (c : Ctx) : Ctx := { c with
    canFail := bodyFail, inLoop := false, inRepeat := true, forBreakSlot := none, forBreakCapture := none,
    refineExits := { c.refineExits with brk := none },
    forExitPacket := failure.orElse fun _ => c.forExitPacket }
  -- elaborate the filters of one generator (in a failure context)
  let elabFilters (c : Ctx) (fs : List SExpr) : EM (Expr × Ctx) := do
    match fs with
    | [] => return (.lit (.logic true), c)
    | _ =>
      let (r, c') ← elabSeq { c with canFail := true, inTaking := true } fs none
      return (← inferable r, c')
  -- The ordinary composed/exclusive paths use the same handoff as a
  -- refining path. Probe a suffix once at its binding's common type;
  -- type-only probes recurse through these same shared suffixes.
  let stagedSuffix (c : Ctx) (q : Pos) (name : String) (bty : Ty)
      (alts rest : List SExpr) (bd : SExpr) (flat : Option Bool := none)
      (extraTops : List STop := []) :
      EM (Option (Choice.FirstLift × Choice.ForStagePlan × Ty × Bool)) := do
    let sourceFail := match bd with
      | .app _ (.ident _ f) [_, .ident _ mode, _] false =>
        if f == "$forReturns" || f == "$forReturnBody" then mode == "true" else bodyFail
      | _ => bodyFail
    if (stagePlan.isNone && (!c.suspends || sourceFail)) ||
        c.inCtor || c.inBlock || c.inDefer then return none
    checkNewLocal c q name
    let before ← get
    let slot ← fresh bty
    let bound := { c with locals := { name, slot, ty := bty, mutable := false } :: c.locals }
    let required := if stagePlan.isSome then stageBorrows else []
    let written := SExpr.block q (rest ++ [bd] ++ required.map (SExpr.ident q ·))
    let caps := (Choice.namesUsed written).eraseDups.filterMap bound.lookup
    let key := "stageOrdinary" ++ contKey bound q name (alts ++ rest ++ [bd]) ++
      forStageCaptureKey bound stageArgs caps
    let known := c.types.loopRequests.findSome? (fun l => l.stagePlan.filter (·.key == key))
    let value? ← if let some outer := stagePlan then do
        let subst := (outer.tparams.map (·.name)).zip (stageArgs.map Ty.toSTy)
        pure (some (← resolveTy c.types q (outer.value.substNames subst), true, before.fx, outer.sourceSuspends))
      else if let some plan := known then
        pure (some (← resolveTy c.types q plan.value, true, before.fx, plan.sourceSuspends))
      else tryCatch (do
        let r ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
          { bound with typeOnly := true } p rest bd (prepared := true) (firstDecides := true)
        let .arr value := r.ty | pure none
        let after ← get
        pure (some (value, forContWaits c before after [r.e], after.fx,
          before.pendingSourceSuspends != after.pendingSourceSuspends || c.sourceWaits r.e))) (fun _ => pure none)
    set before
    let some (value, waits, effects, sourceSuspends) := value? | return none
    if stagePlan.isNone && !waits && forBodySafe c bd then return none
    -- Refining lifts can infer their effects. Their initially empty fnFx
    -- is not an explicit computes restriction; retain the suffix's typed
    -- effects, as immediate continuations do, and expose them to a parent
    -- type-only probe as well.
    let allowed := heapFx.filter fun fx => c.fnFx.contains fx || effects.any (·.1 == fx) ||
      (stagePlan.orElse fun _ => known).any (·.specs.contains fx)
    let bound := { bound with fnFx := allowed }
    let request ← match forStagePlanOf bound q key rest bd value ((stagePlan.map (·.outcome)).getD bodyFail) required sourceSuspends with
      | .ok request => pure request
      | .error _ => return none
    let some plan := request.stagePlan | return none
    let args := plan.tparams.map fun tp =>
      (c.types.tvars.lookup tp.name).getD (.param tp.name (tp.constraint == "comparable"))
    let flatten := stagePlan.isSome && flat.getD stageFlat
    let prepare ← match forStagePrefixOf bound plan args q rest bd flatten with
      | .ok prepare => pure prepare
      | .error _ => return none
    let prepare := { prepare with extraFns := prepare.extraFns ++ extraTops }
    let hasPlan := c.types.loopRequests.any (·.key == request.key)
    let hasPrefix := c.types.loopRequests.any (·.key == prepare.key)
    modify fun st => { st with
      fx := effects,
      pendingSourceSuspends := st.pendingSourceSuspends + (if sourceSuspends then 1 else 0) }
    noteFx q (heapFx.filter fun fx => (stagePlan.orElse fun _ => known).any (·.specs.contains fx))
      (some prepare.name)
    if !c.typeOnly then
      for req in (if hasPlan then [] else [request]) ++ (if hasPrefix then [] else [prepare]) do
        modify fun st => { st with loopFirst := st.loopFirst ++
          [{ g := "", pos := q, itemCode := .lit .void, argSet := none, lift := .ok req }] }
      modify fun st => { st with
        forStageUses := st.forStageUses + 1,
        pendingSuspendingCasts := st.pendingSuspendingCasts + (if c.suspends && (!hasPlan || !hasPrefix) then 1 else 0),
        pendingWaitingCasts := st.pendingWaitingCasts + (if c.suspends && (!hasPlan || !hasPrefix) then 1 else 0) }
    else
      -- A type-only parent must still see the wait hidden by this staged
      -- placeholder, including a function-value call in a nested for.
      modify fun st => { st with
        pendingSuspendingCasts := st.pendingSuspendingCasts + 1,
        pendingWaitingCasts := st.pendingWaitingCasts + 1 }
    return some (prepare, plan, value, !c.typeOnly && hasPlan && hasPrefix)
  -- (`peel`: the first group's filter, then its values, failing where the
  -- filter fails, without the loop over its one element: a continuation's
  -- clauses, #335)
  let rec build (c : Ctx) (gs : List (SExpr × List SExpr)) (bd : SExpr)
      (stageHere : Bool := true) (flatOverride : Option Bool := none) (peel : Bool := false) : EM R := do
    if let some plan := stagePlan.filter (fun _ => stageHere) then
      let clauses := gs.flatMap fun (g, fs) => g :: fs
      let (req, obj, ty) ← match forStageEnvOf { c with forStageArgs := stageArgs, forStageFlat := flatOverride.getD stageFlat, forStageCopies := stageCopies, forStageBorrows := stageBorrows } plan p clauses bd with
        | .ok r => pure r
        | .error why => eerr p s!"cannot stage this for: {why} (#417)"
      let r ← if c.types.loopRequests.any (·.key == req.key) then do
          -- Only this synthetic environment allocation is an implementation
          -- effect. Its fields are local reads, evaluated before allocation.
          let fx := (← get).fx
          let r ← elabE c obj (some ty)
          let e ← coerce p r ty
          modify fun st => { st with fx }
          pure (⟨e, ty⟩ : R)
        else do
          modify fun st => { st with loopFirst := st.loopFirst ++
            [{ g := "", pos := p, itemCode := .lit .void, argSet := none, lift := .ok req }] }
          pure (⟨.prim .userErr [], ty⟩ : R)
      if gs.isEmpty then return r
      return ⟨.prim .mkArr [r.e], .arr r.ty⟩
    -- (#314) filters `fs` with an exclusive choice among them, then the
    -- groups `more`: its guards pick a path into a selector; each path's
    -- clauses up to its first generator (its guards again, which bind its
    -- names, its clauses, then the filters after the choice) go into this
    -- filter under the selector, so a failure there rolls back to this
    -- iteration's generator; each path's generators into the iteration's
    -- body, under it. The filter's code, the body's (an array of the
    -- values), and their type.
    let rec exclIter (c : Ctx) (fs : List SExpr) (more : List (SExpr × List SExpr))
        (bd : SExpr) (stageOverride : Option Bool := none) : EM (Expr × Expr × Ty) := do
      match fs.findIdx? isExcl with
      | none =>
        let (filt, c') ← elabFilters c fs
        let inner ← build c' more bd (flatOverride := stageOverride)
        match more with
        | [] => return (filt, .prim .mkArr [inner.e], inner.ty)
        | _ => match inner.ty with
          | .arr t => return (filt, inner.e, t)
          | _ => eerr p "internal: nested for"
      | some j =>
        let (codeA, cA) ← elabFilters c (fs.take j)
        let after := fs.drop (j + 1)
        let moreCl := more.flatMap fun (g', fs') => g' :: fs'
        -- A refining condition must remain with the branch. A safe body
        -- can run inside $forFirst with the suffix: its first segment
        -- still belongs to this filter, and later generators keep their
        -- effects even when empty. The option prevents failure of a
        -- selected branch from choosing the else branch instead.
        if let some b@{ branchy := some i, .. } := fs[j]?.bind Choice.binding? then
          let i := pruneMethodCases cA i
          let st ← get
          let (_, ty, _, refined) ← elabBranchAlts { cA with canFail := true, inTaking := true, typeOnly := true }
            b.pos i b.ty b.place
          restoreConstructProbe cA st
          if refined && stagePlan.isNone && forBodySafe cA bd then
            checkNewLocal cA b.pos b.name
            if cA.typeOnly then
              let slot ← fresh ty
              let cB := { cA with locals := { name := b.name, slot, ty, mutable := false } :: cA.locals }
              let (f, a, t) ← exclIter cB after more bd stageOverride
              return (.seq codeA f, a, t)
            let restCl := after ++ moreCl
            let key := (if bodyFail then "fo" else "f") ++ contKey cA b.pos b.name (i :: restCl ++ [bd])
            let req := cA.types.loopRequests.find? (·.key == key)
            let fits (l : Choice.FirstLift) : Bool :=
              cA.acceptsHelper l
            if req.isNone && (contForLiftOf cA b.pos b.name ty .void [i] restCl bd bodyFail).toOption.isSome then
              -- Elaborate the suffix once, in its source context. Otherwise
              -- an inner lift can retain an outer var's old name after the
              -- enclosing lift has renamed it for mutable copy-out.
              let st0 ← get
              let slot ← fresh ty
              let cB := { cA with locals := { name := b.name, slot, ty, mutable := false } :: cA.locals }
              let values ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
                cB p restCl bd (prepared := true) (firstDecides := true)
                  (failure := if bodyFail then some (.app p (.ident p "Err") [] false) else none)
              let .arr t := values.ty | eerr b.pos "internal: a refining for's suffix"
              if forContWaits cA st0 (← get) [values.e] then set st0 else
                match contForLiftOf cA b.pos b.name ty t [i] restCl bd bodyFail with
                | .ok lift =>
                  -- This body moves to an immediate helper. Its trial's
                  -- source-frame locals/cast requests do not exist in the
                  -- final suspending caller; discover them in the helper.
                  if cA.suspends then restoreForContTrial st0
                  modify fun st => { st with loopFirst := st.loopFirst ++
                    [{ g := "", pos := b.pos, itemCode := .lit .void, argSet := none, lift := .ok lift }] }
                  return (codeA, .prim .userErr [], t)
                | .error why => eerr b.pos s!"cannot share the refining for's suffix: {why} (#417)"
            if let some l := req.filter fits then
              let kv := s!"$refineFor{b.pos.line}_{b.pos.col}{b.name}v"
              let kt := kv ++ "t"
              let elem := kv ++ "e"
              let call := SExpr.app b.pos (.ident b.pos l.name) l.args true
              let callCl : List SExpr := if l.sets.isEmpty then [.decl b.pos kv none false call] else
                [.decl b.pos kt none false call] ++
                  l.sets.zipIdx.map (fun (n, j) => SExpr.set b.pos (.ident b.pos n) none
                    (.app b.pos (.ident b.pos kt) [.int b.pos ((j + 1 : Nat) : Int)] false)) ++
                  [.decl b.pos kv none false (.app b.pos (.ident b.pos kt) [.int b.pos 0] false)]
              let site := s!"$refineFor{b.pos.line}_{b.pos.col}{b.name}"
              let consume (arm : SExpr) : SExpr :=
                let cl := Choice.prepare [.decl b.pos b.name (some ty.toSTy) false arm]
                  (choiceValues cA) (choiceField cA) (site := site) (fieldOrder := choiceOrder cA)
                  (keepExcl := true) (keepBranches := choiceHasCast cA)
                let vals : SExpr := if bodyFail then
                  .app b.pos (.ident b.pos "$forOutcomeValues") [.ident b.pos kv] false
                  else .ident b.pos kv
                let clauses := .block b.pos (cl ++ callCl ++ [.gen b.pos elem none vals])
                .optionLit b.pos (if bodyFail then
                    .app b.pos (.ident b.pos "$forFirstOutcome")
                      [clauses, .ident b.pos elem, .app b.pos (.ident b.pos "Err") [] false] false
                  else .app b.pos (.ident b.pos "$forFirst") [clauses, .ident b.pos elem] false)
              let selected := Choice.consumeBranches i site consume
              let values ← elabE { cA with canFail := true, inTaking := true } (.query b.pos selected) none
              let arrTy := if bodyFail then match values.ty with | .opt t => t | t => t else values.ty
              let .arr t := arrTy | eerr b.pos "internal: a refining for's values"
              let slot ← fresh values.ty
              let value ← if bodyFail then forOutcomeValues cA b.pos ⟨.local slot, values.ty⟩ else pure ⟨.local slot, values.ty⟩
              return (.seq codeA (.assign slot values.e), value.e, t)
          -- A waiting body cannot move into a filter-bound continuation.
          -- Prepare only this filter's prefix, then dispatch its typed
          -- environment from the iteration body after the filter commits.
          let sourceFail := match bd with
            | .app _ (.ident _ f) [_, .ident _ mode, _] false =>
              if f == "$forReturns" || f == "$forReturnBody" then mode == "true" else bodyFail
            | _ => bodyFail
          if refined && (stagePlan.isSome || (ctx.suspends && !sourceFail)) &&
              !cA.inCtor && !cA.inBlock && !cA.inDefer then
            checkNewLocal cA b.pos b.name
            let restCl := after ++ moreCl
            if cA.typeOnly then
              let slot ← fresh ty
              let cB := { cA with locals := { name := b.name, slot, ty, mutable := false } :: cA.locals }
              let (f, a, t) ← exclIter cB after more bd stageOverride
              return (.seq codeA f, a, t)
            let rootCaptures := (Choice.namesUsed (.block p (i :: restCl ++ [bd]))).filterMap cA.lookup
            let key := "stage" ++ contKey cA b.pos b.name (i :: restCl ++ [bd]) ++
              forStageCaptureKey cA [] (rootCaptures.filter (·.storage.isSome))
            let plan? := stagePlan.orElse fun _ =>
              cA.types.loopRequests.findSome? (fun l => l.stagePlan.filter (·.key == key))
            if plan?.isNone then
              let saved ← get
              let slot ← fresh ty
              let cB := { cA with
                typeOnly := true, forStage := none,
                locals := { name := b.name, slot, ty, mutable := false } :: cA.locals }
              let values ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
                cB p restCl bd (prepared := true) (firstDecides := true)
              let .arr value := values.ty | eerr b.pos "internal: staged for result"
              let effects := (← get).fx
              let sourceSuspends := saved.pendingSourceSuspends != (← get).pendingSourceSuspends || cA.sourceWaits values.e
              set { saved with
                fx := effects,
                pendingSourceSuspends := saved.pendingSourceSuspends + (if sourceSuspends then 1 else 0) }
              let allowed := heapFx.filter fun k => cA.fnFx.contains k || effects.any (·.1 == k)
              let req ← match forStagePlanOf { cA with fnFx := allowed } b.pos key (i :: restCl) bd value bodyFail [] sourceSuspends with
                | .ok req => pure req
                | .error why => eerr b.pos s!"cannot stage this refining for: {why} (#417)"
              modify fun st => { st with
                loopFirst := st.loopFirst ++ [{ g := "", pos := b.pos, itemCode := .lit .void, argSet := none, lift := .ok req }],
                pendingSuspendingCasts := st.pendingSuspendingCasts + 1,
                pendingWaitingCasts := st.pendingWaitingCasts + 1,
                forStageUses := st.forStageUses + 1 }
              return (codeA, .prim .userErr [], value)
            let some plan := plan? | eerr b.pos "internal: staged for plan"
            if plan.sourceSuspends then
              modify fun st => { st with pendingSourceSuspends := st.pendingSourceSuspends + 1 }
            noteFx b.pos (heapFx.filter plan.specs.contains)
            let site := s!"{plan.base}$selected"
            let rootArgs := if stagePlan.isSome then stageArgs else
              plan.tparams.map fun tp => (cA.types.tvars.lookup tp.name).getD (.param tp.name (tp.constraint == "comparable"))
            let copyNames := if stagePlan.isSome then stageCopies else plan.copies.map (·.1)
            let borrowNames := if stagePlan.isSome then stageBorrows else plan.borrowed
            let suffixCtx := { cA with
              fnFx := heapFx.filter (fun k => cA.fnFx.contains k || plan.specs.contains k),
              locals := { name := b.name, slot := 0, ty, mutable := false } :: cA.locals }
            let viewSub := (plan.tparams.map (·.name)).zip (rootArgs.map Ty.toSTy)
            let resultTy ← resolveTy cA.types b.pos (plan.value.substNames viewSub)
            let tailKey := "tail" ++ contKey suffixCtx b.pos b.name (restCl ++ [bd]) ++ reprStr resultTy ++
              forStageCaptureKey cA rootArgs (borrowNames.filterMap cA.lookup)
            let nextReq ← match forStagePlanOf suffixCtx b.pos tailKey restCl bd resultTy plan.outcome borrowNames plan.sourceSuspends with
              | .ok req => pure req
              | .error why => eerr b.pos s!"cannot type this waiting for's suffix: {why} (#417)"
            if !cA.types.loopRequests.any (·.key == nextReq.key) then
              modify fun st => { st with loopFirst := st.loopFirst ++
                [{ g := "", pos := b.pos, itemCode := .lit .void, argSet := none, lift := .ok nextReq }] }
              return (codeA, .prim .userErr [], if stagePlan.isSome then Ty.struct plan.base rootArgs else resultTy)
            let some nextPlan := nextReq.stagePlan | eerr b.pos "internal: missing suffix plan"
            let nextArgs := nextPlan.tparams.map fun tp =>
              (cA.types.tvars.lookup tp.name).getD (.param tp.name (tp.constraint == "comparable"))
            let nextCopies := nextPlan.copies.map (·.1)
            let nextBorrows := nextPlan.borrowed
            let suffix ← match forStagePrefixOf suffixCtx nextPlan nextArgs b.pos restCl bd (stageOverride.getD stageFlat) nextCopies nextBorrows with
              | .ok req => pure req
              | .error why => eerr b.pos s!"cannot share this waiting for's suffix: {why} (#335, #417)"
            if !cA.types.loopRequests.any (·.key == suffix.key) then
              modify fun st => { st with loopFirst := st.loopFirst ++
                [{ g := "", pos := b.pos, itemCode := .lit .void, argSet := none, lift := .ok suffix }] }
              return (codeA, .prim .userErr [], if stagePlan.isSome then Ty.struct plan.base rootArgs else resultTy)
            let stageTypes := rootArgs.map Ty.toSTy
            let consume (arm : SExpr) : SExpr :=
              let clauses := Choice.prepare [.decl b.pos b.name (some ty.toSTy) false arm]
                (choiceValues cA) (choiceField cA) (site := site) (fieldOrder := choiceOrder cA)
                (keepExcl := true) (keepBranches := choiceHasCast cA)
              let payload := site ++ "$suffix"
              let packet := payload ++ "$packet"
              let call := SExpr.app b.pos (.ident b.pos suffix.name) suffix.args true
              let get (j : Nat) := SExpr.app b.pos (.ident b.pos packet) [.int b.pos (j : Int)] false
              let tail : List SExpr := if nextCopies.isEmpty then [.decl b.pos payload none false call] else
                .decl b.pos packet none false call ::
                  (nextCopies.zipIdx.map fun (n, j) => .set b.pos (.ident b.pos n) none
                    (.app b.pos (.ident b.pos "$refineCopyOut") [get (j + 1)] false)) ++
                  [.decl b.pos payload none false (get 0)]
              let clauses := clauses ++ tail
              let body := forStageBodyAs bd (.app b.pos (.ident b.pos "$forResumeValues") [.ident b.pos payload, forStageCopyMetadata b.pos nextCopies, .block b.pos (nextBorrows.map (SExpr.ident b.pos ·))] false)
              if stagePlan.isSome then
                let stage := SExpr.app b.pos (.ident b.pos "$forStage")
                  [.str b.pos [.text plan.base], .decl b.pos "$stageView" (some (forStageView plan.base stageTypes)) false (.tuple b.pos []),
                    forStageCopyMetadata b.pos copyNames, .block b.pos (borrowNames.map (SExpr.ident b.pos ·)), .ident b.pos "false", .ident b.pos "true", .block b.pos clauses, body] false
                .optionLit b.pos (forClauseExitScope bd stage)
              else
              let prepare := SExpr.app b.pos (.ident b.pos "$forPrepare")
                [.str b.pos [.text plan.base], .decl b.pos "$stageView" (some (forStageView plan.base stageTypes)) false (.tuple b.pos []),
                  forStageCopyMetadata b.pos copyNames, .block b.pos (borrowNames.map (SExpr.ident b.pos ·)), .ident b.pos "true", .block b.pos clauses, body] false
              let code := if plan.copies.isEmpty then prepare else
                let packet := site ++ "$packet"
                let get (j : Nat) := SExpr.app b.pos (.ident b.pos packet) [.int b.pos (j : Int)] false
                SExpr.block b.pos (.decl b.pos packet none false prepare ::
                  (copyNames.zipIdx.map fun (n, j) => .set b.pos (.ident b.pos n) none
                    (.app b.pos (.ident b.pos "$refineCopyOut") [get (j + 1)] false)) ++ [get 0])
              .optionLit b.pos code
            let selected := Choice.consumeBranches i site consume
            let values ← elabE { cA with canFail := true, inTaking := true }
              (.query b.pos selected) none
            let slot ← fresh values.ty
            if stagePlan.isSome then
              let .arr value := values.ty | eerr b.pos "internal: prepared for environments"
              return (.seq codeA (.assign slot values.e), .local slot, value)
            let ready := site ++ "$ready"
            let c := { bodyCtx cA with
              canFail := sourceFail,
              locals := { name := ready, slot, ty := values.ty, mutable := false } :: cA.locals }
            let resumed ← elabE c (.app b.pos (.ident b.pos "$forResumeValues") [.ident b.pos ready, forStageCopyMetadata b.pos copyNames, .block b.pos (borrowNames.map (SExpr.ident b.pos ·))] false) none
            modify fun st => { st with forStageUses := st.forStageUses + 1 }
            let .arr value := resumed.ty | eerr b.pos "internal: staged for values"
            return (.seq codeA (.assign slot values.e), resumed.e, value)
          let cl := pruneMethodBinding cA (fs[j]?.getD (.tuple p []))
          let (f, a, t) ← exclIter cA (Choice.bifToExcl cl ++ after) more bd stageOverride
          return (.seq codeA f, a, t)
        let some (.decl gp x xty _ (.app _ _ alts _)) := fs[j]? | eerr p "internal: an exclusive choice"
        let altsS := alts.filter (!Choice.isJoinOf ·)
        -- (an `if`'s, #331, with no type written: its branches' join; a
        -- branch with a call to lift typed as `option{…}` takes it, #283)
        let xty ← match xty with
          | none => joinOfType elabBranchAlts cA gp alts
          | t => pure t
        let alts : List (List SExpr × SExpr) := alts.filterMap fun
          | .app _ (.ident _ "$alt") [.block _ gs, r] false => some (gs, r)
          | _ => none
        -- (the selector: the first alternative whose guards hold)
        let selS : SExpr := alts.zipIdx.foldr (fun ((gs, _), i) acc =>
          .ite gp gs (.int gp (i : Int)) (some acc)) (.int gp (-1))
        let rsel ← elabE { cA with canFail := true, inTaking := true } selS (some .int)
        let sel ← fresh .int
        -- (a path's clauses: its guards, then its value bound to the choice's name)
        let liftP (gs : List SExpr) (r : SExpr) (i : Nat) : List SExpr :=
          let rcl : List SExpr := match r with
            | .block rp ss => match ss.getLast? with
              | some (.decl q y t v e) => ss.dropLast ++ [.decl q y t v e, .decl rp x xty false (.ident rp y)]
              | some l => ss.dropLast ++ [.decl rp x xty false l]
              | none => [.decl rp x xty false (.tuple rp [])]
            | e => [.decl e.pos x xty false e]
          normGens (Choice.prepare (gs ++ rcl) (choiceValues cA) (choiceField cA)
            (site := s!"$x{x}a{i}") (fieldOrder := choiceOrder cA) (keepExcl := true)
            (keepBranches := choiceHasCast cA))
        -- (a path: its clauses up to its first generator into this filter, its
        -- generators into the body, with `pb` as the body; `flat`: `pb` is an
        -- array of the values, a continuation's, to flatten)
        let runPath (cl : List SExpr) (pb : SExpr) (flat : Bool) : EM (Expr × Expr × Ty) := do
          let transfer := if stagePlan.isSome && flat then some true else stageOverride
          let (f, a, t) ← exclIter cA (cl.takeWhile (!isGen ·)) (groups (cl.dropWhile (!isGen ·))) pb transfer
          if !flat || stagePlan.isSome then return (f, a, t)
          match t with
          | .arr t' => return (f, .prim .flatten [← inferable ⟨a, .arr t⟩], t')
          | _ => eerr gp "internal: a continuation's values"
        -- (#335, phase 2b: another such choice, or an exclusive one, in the
        -- clauses after it, and a body that may run in a failure context:
        -- those clauses and the body a function of their own, #342's, which
        -- each path calls, instead of a copy in each)
        let restCl := after ++ moreCl
        let staged ← if restCl.any isCF then
            match xty with
            | some ty => do
              let bty ← resolveTy cA.types gp ty
              stagedSuffix cA gp x bty altsS restCl bd stageOverride
            | none => pure none
          else pure none
        if let some (_, _, value, false) := staged then
          let value := (stagePlan.map fun plan => Ty.struct plan.base stageArgs).getD value
          return (codeA, .prim .userErr [], value)
        let contOK := stagePlan.isNone && restCl.any isCF && forBodySafe cA bd && xty.isSome
        let req := if !contOK || cA.typeOnly then none else
          cA.types.loopRequests.find? (·.key == (if bodyFail then "fo" else "f") ++ contKey cA gp x (altsS ++ restCl ++ [bd]))
        let fits (l : Choice.FirstLift) : Bool :=
          cA.acceptsHelper l
        let kv := s!"$xk{gp.line}_{gp.col}{x}v"
        let plan : List (List SExpr × SExpr × Bool) ← if let some (prepare, plan, _, true) := staged then
            let (callCl, resumed) := forStageInvoke gp prepare plan.borrowed bd
            pure (alts.zipIdx.map fun ((gs, r), i) => (liftP gs r i ++ callCl, resumed, true))
          else match req with
          | some l =>
            if fits l then
              let call : SExpr := .app gp (.ident gp l.name) l.args true
              let callCl : List SExpr := if l.sets.isEmpty then [.decl gp kv none false call] else
                let kt := s!"$xk{gp.line}_{gp.col}{x}t"
                [.decl gp kt none false call] ++
                  l.sets.zipIdx.map (fun (m, j) => SExpr.set gp (.ident gp m) none (.app gp (.ident gp kt) [.int gp ((j + 1 : Nat) : Int)] false)) ++
                  [.decl gp kv none false (.app gp (.ident gp kt) [.int gp 0] false)]
              let vals : SExpr := if bodyFail then .app gp (.ident gp "$forOutcomeValues") [.ident gp kv] false else .ident gp kv
              pure (alts.zipIdx.map fun ((gs, r), i) => (liftP gs r i ++ callCl, vals, true))
            else pure (alts.zipIdx.map fun ((gs, r), i) => (liftP gs r i ++ restCl, bd, false))
          | none =>
            -- (the first elaboration: the first path with the clauses after
            -- it and the body, for the values' type, which asks for the
            -- function; its code is not kept, as the next round compiles all)
            if let (true, some ((gs0, r0), some sty)) := (contOK && !cA.typeOnly, alts.head?.map (·, xty)) then
              let bty ← resolveTy cA.types gp sty
              -- (what refuses it known before the trial, which then costs
              -- nothing: all but the values' type, #364's review)
              if (contForLiftOf cA gp x bty .void altsS restCl bd bodyFail).toOption.isSome then
                let st0 ← get
                let (f0, a0, t0) ← runPath (liftP gs0 r0 0 ++ restCl) bd false
                if forContWaits cA st0 (← get) [f0, a0] then set st0 else
                  match contForLiftOf cA gp x bty t0 altsS restCl bd bodyFail with
                  | .ok lift =>
                    if cA.suspends then restoreForContTrial st0
                    let use : LoopUse := { g := "", pos := gp, itemCode := .lit .void, argSet := none, lift := .ok lift }
                    modify fun st => { st with loopFirst := st.loopFirst ++ [use] }
                    if cA.suspends then return (codeA, .prim .userErr [], t0)
                    return (Expr.seq codeA f0, a0, t0)
                  | .error _ => set st0
            pure (alts.zipIdx.map fun ((gs, r), i) => (liftP gs r i ++ restCl, bd, false))
        let mut filts : Array Expr := #[]
        let mut arrs : Array Expr := #[]
        let mut ety : Option Ty := none
        for (cl, pb, flat) in plan do
          let (f, a, t) ← runPath cl pb flat
          if let some t0 := ety then
            if t0 != t then eerr gp s!"the for's values have the type {t0.show} on one path of this if and {t.show} on another"
          ety := some t
          filts := filts.push f
          arrs := arrs.push a
        let some t := ety | eerr gp "internal: an exclusive choice without alternatives"
        let pick (es : Array Expr) (last : Expr) : Expr :=
          (es.toList.zipIdx.foldr (fun (e, i) acc => .ite (p2 .eq (.local sel) (.lit (.int (i : Int)))) e acc) last)
        -- (each path's filter as `void`, as `failV` is, for the if-chain)
        let filt := Expr.seq codeA (.seq (.assign sel rsel.e)
          (pick (filts.map fun f => Expr.seq f (.lit .void)) Expr.failV))
        return (filt, pick arrs (.lit Value.emptyArray), t)
    match gs with
    | [] =>
      let r ← elabE (bodyCtx c) bd none
      -- The generated arrays must infer their element type during
      -- suspension lowering. As for array/tuple literals, a body that
      -- never completes has Core's void type without changing its exit.
      let r := if r.ty == .never then { r with e := .seq r.e (.lit .void) } else r
      if let some failed := failure then
        -- Waiting source bodies cannot fail. Their explicit source exits
        -- already return packets, so no failure-capture rewrite is needed.
        if c.suspends && !r.e.mayFail ctx.sigProg then return r
        let packet ← elabE { c with canFail := false } failed (some c.retTy)
        let hint ← fresh (.opt r.ty)
        return ⟨FailCapture.marked hint r.e (.ret packet.e), r.ty⟩
      return r
    | (g, fs) :: more =>
      let declare (c : Ctx) (n : String) (ty : Ty) : EM (Nat × Ctx) := do
        if c.lookup n |>.isSome then eerr g.pos s!"'{n}' is already defined"
        let slot ← fresh ty
        return (slot, { c with locals := { name := n, slot, ty, mutable := false } :: c.locals })
      -- (a choice whose alternatives have several values themselves, or
      -- clauses to lift, #283: a for of its own for each alternative, with
      -- the clauses after it and the body, their values concatenated, so
      -- that each alternative's values come in order, with the body between)
      if let some b@{ pos := gp, .. } := Choice.binding? g then
        if b.composed then
          -- (with the binding's name: an inlined body's position is every
          -- site's, #314)
          let site := s!"$cf{gp.line}_{gp.col}{b.name}"
          let moreClauses := more.flatMap fun (g', fs') => g' :: fs'
          let bctx : Ctx := { c with canFail := ctx.canFail && !firstDecides, inTaking := ctx.inTaking, inLoop := ctx.inLoop,
                                     inRepeat := ctx.inRepeat }
          let liftA (a : SExpr) (i : Nat) : List SExpr :=
            -- (its exclusive choices kept: this for compiles them, #314)
            Choice.prepare [.decl gp b.name b.ty false a] (choiceValues c) (choiceField c)
              (fieldOrder := choiceOrder c)
              (site := s!"{site}a{i}") (keepExcl := true) (keepBranches := choiceHasCast c)
          let forW (cl : List SExpr) (bd : SExpr) : EM R :=
            elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq bctx p cl bd
              (prepared := true) (failure := failure)
          -- (#335, phase 2: another such choice, or an exclusive one, in the
          -- clauses after it, and a body that may run in a failure context:
          -- those clauses and the body a function of their own, which each
          -- alternative's for calls, instead of a copy in each)
          let restCl := fs ++ moreClauses
          if c.suspends then
            let saved ← get
            let mut types : List Ty := []
            for (a, i) in b.alts.zipIdx do
              let r ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
                { bctx with typeOnly := true } p (liftA a i) (.ident gp b.name) (prepared := true)
              if let .arr t := r.ty then types := types ++ [t]
            set saved
            if types.length == b.alts.length then
              let stem := s!"$choiceType{(contKey c gp b.name (b.alts ++ restCl ++ [bd])).hash}"
              if let some typing := choiceTypePlan c stem b.name types (restCl ++ [bd]) then
                let polymorphic := !typing.params.isEmpty
                if !c.constructProbe && (!types.all (some · == types.head?) || restCl.any isCF) then
                  let before ← get
                  let operations ← choiceOperations elabE c stem b.name typing (restCl ++ [bd]) (forBody := some bd)
                  let typing := operations.plan
                  let poly ← operations.context (← if polymorphic then choiceTypeContext c typing else pure c)
                  let staged ← stagedSuffix poly gp b.name typing.binding b.alts
                    (restCl.map operations.rewrite) (operations.rewrite bd) (extraTops := operations.extraFns)
                  let after ← get
                  set { after with nslots := before.nslots, slotTys := before.slotTys }
                  if let some (prepare, plan, value, ready) := staged then
                    let joined := if polymorphic then choiceResultType c.types (typing.instances.map (value.subst ·)) else some value
                    if let some value := joined then
                      if !ready then return ⟨.prim .userErr [], .arr value⟩
                      let (callCl, resumed) := forStageInvoke gp prepare plan.borrowed bd
                      let mut parts : List R := []
                      for (a, i) in b.alts.zipIdx do
                        let r ← forW (liftA a i ++ (operations.casePrelude[i]?.getD []) ++ callCl) resumed
                        let r ← if polymorphic then do
                            let ty := Ty.arr (.arr value)
                            pure (⟨← coerce gp r ty, ty⟩ : R)
                          else pure r
                        let .arr (.arr t) := r.ty | eerr gp "internal: a staged continuation's values"
                        parts := parts ++ [⟨.prim .flatten [← inferable r], .arr t⟩]
                      let some first := parts.head? | eerr gp "internal: a choice without alternatives"
                      return ⟨parts.tail.foldl (fun acc r => p2 .concat acc r.e) first.e, first.ty⟩
          -- Failable bodies return outcomes so failure stops the entire
          -- for, rather than merely rejecting one continuation call.
          if forBodySafe c bd then
            let req := if c.typeOnly then none else
              c.types.loopRequests.find? (·.key == (if bodyFail then "fo" else "f") ++ contKey c gp b.name (b.alts ++ restCl ++ [bd]))
            let fits (l : Choice.FirstLift) : Bool :=
              c.acceptsHelper l
            if let some l := req then
              if fits l then
                let kv := s!"{site}v"
                let mut parts : List R := []
                for (a, i) in b.alts.zipIdx do
                  let call : SExpr := .app gp (.ident gp l.name) l.args true
                  let callCl : List SExpr := if l.sets.isEmpty then continuationBind gp l kv call else
                    let kt := s!"{site}t"
                    continuationBind gp l kt call ++
                      l.sets.zipIdx.map (fun (m, j) => SExpr.set gp (.ident gp m) none (.app gp (.ident gp kt) [.int gp ((j + 1 : Nat) : Int)] false)) ++
                      [.decl gp kv none false (.app gp (.ident gp kt) [.int gp 0] false)]
                  let vals : SExpr := if bodyFail then .app gp (.ident gp "$forOutcomeValues") [.ident gp kv] false else .ident gp kv
                  let r ← forW (liftA a i ++ (l.casePrelude[i]?.getD []) ++ callCl) vals
                  match r.ty with
                  | .arr (.arr t) => parts := parts ++ [⟨.prim .flatten [← inferable r], .arr t⟩]
                  | _ => eerr gp "internal: a continuation's values"
                let some r0 := parts.head? | eerr gp "internal: a choice without alternatives"
                return ⟨parts.tail.foldl (fun acc r => p2 .concat acc r.e) r0.e, r0.ty⟩
            else if let some a0 := b.alts.head? then
              -- (the first elaboration: each alternative alone, for its
              -- binding's type, and the first with the clauses after it and
              -- the body, for the values' type; its code is not kept)
              let st0 ← get
              let mut tys : List Ty := []
              for (a, i) in b.alts.zipIdx do
                let r ← forW (liftA a i) (.ident gp b.name)
                if let .arr t := r.ty then tys := tys ++ [t]
              let same := tys.length == b.alts.length && tys.all (some · == tys.head?)
              -- (what refuses it known before the trial, which then costs nothing)
              -- (all its refusals but the values' type, #364's review)
              let known : Bool := match tys.head? with
                | some bty => (contForLiftOf c gp b.name bty .void b.alts restCl bd bodyFail).toOption.isSome
                | none => false
              if same && known && restCl.any isCF then
                let r0 ← forW (liftA a0 0 ++ restCl) bd
                if forContWaits c st0 (← get) [r0.e] then set st0 else
                  match (do
                      let some bty := tys.head? | throw "no type"
                      let .arr vty := r0.ty | throw "no values"
                      contForLiftOf c gp b.name bty vty b.alts restCl bd bodyFail) with
                  | .ok lift =>
                    if c.suspends then restoreForContTrial st0
                    let use : LoopUse := { g := "", pos := gp, itemCode := .lit .void, argSet := none, lift := .ok lift }
                    modify fun st => { st with loopFirst := st.loopFirst ++ [use] }
                    if c.suspends then return ⟨.prim .userErr [], r0.ty⟩
                    return r0
                  | .error _ => set st0
              else if !same && tys.length == b.alts.length && !c.constructProbe then
                let stem := s!"$choiceType{(contKey c gp b.name (b.alts ++ restCl ++ [bd])).hash}"
                let some plan := choiceTypePlan c stem b.name tys (restCl ++ [bd])
                  | eerr gp "internal: a composed choice without value types"
                let before ← get
                modify fun st => { st with fx := [] }
                let trial ← tryCatch (do
                  let operations ← choiceOperations elabE c stem b.name plan (restCl ++ [bd]) (forBody := some bd)
                  let plan := operations.plan
                  let poly ← operations.context (← choiceTypeContext c plan)
                  let slot ← fresh plan.binding
                  let bound := { poly with
                    typeOnly := true,
                    locals := { name := b.name, slot, ty := plan.binding, mutable := false } :: poly.locals }
                  let r ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
                    bound p (restCl.map operations.rewrite) (operations.rewrite bd) (prepared := true) (failure := failure)
                  -- With no remaining clauses, ordinary elabFor returns
                  -- the body itself; the generated $forFirst wraps it in
                  -- one array, even when the body is another for.
                  let r : R := if restCl.isEmpty then ⟨.prim .mkArr [r.e], .arr r.ty⟩ else r
                  if forContWaits c before (← get) [r.e] then return none
                  let .arr value := r.ty | return none
                  let some result := choiceResultType c.types (plan.instances.map (r.ty.subst ·)) | return none
                  let effects := (← get).fx
                  let allowed := heapFx.filter fun k => c.fnFx.contains k || effects.any (·.1 == k)
                  let lift ← match contForLiftOf { poly with fnFx := allowed } gp b.name plan.binding value b.alts
                    (restCl.map operations.rewrite) (operations.rewrite bd) bodyFail with
                    | .ok lift =>
                      let key := (if bodyFail then "fo" else "f") ++ contKey c gp b.name (b.alts ++ restCl ++ [bd])
                      joinedChoiceResult poly plan (operations.lift key lift)
                    | .error _ => return none
                  return some (lift, result, effects)) (fun _ => pure none)
                set before
                if let some (lift, result, effects) := trial then
                  modify fun st => { st with loopFirst := st.loopFirst ++
                    [{ g := "", pos := gp, itemCode := .lit .void, argSet := none, lift := .ok lift }] }
                  for (k, q, via) in effects do noteFx q [k] via
                  return ⟨.prim .userErr [], result⟩
                set st0
              else set st0
          let mut parts : List R := []
          for (a, i) in b.alts.zipIdx do
            parts := parts ++ [← forW (liftA a i ++ fs ++ moreClauses) bd]
          let some r0 := parts.head? | eerr gp "internal: a choice without alternatives"
          if let some r := parts.find? (·.ty != r0.ty) then
            eerr gp s!"the for's values have the type {r0.ty.show} for one alternative of this choice and {r.ty.show} for another"
          return ⟨parts.tail.foldl (fun acc r => p2 .concat acc r.e) r0.e, r0.ty⟩
      -- (a call of a recursive function with several values taken lazily,
      -- #246: a loop over its values, each one iteration, over a one-element
      -- array, whose filter binds it and runs the generator's filters, and
      -- whose values are collected)
      if let some { pos := gp, name := n, ty := sty, each := some (.app _ (.ident _ "$loop") lp false), .. } :=
          Choice.binding? g then
        let lg ← elabLoopGen { c with canFail := true, inTaking := true } gp lp
        let ty ← match ← sty.mapM (resolveTy c.types gp) with
          | some t => pure t
          | none => pure lg.vty
        let (xs, c1) ← declare c n ty
        -- (the iteration's values, their type, and whether they are flat
        -- already: with an exclusive choice among the filters, #314, its
        -- paths in this filter and their values, flattened)
        let (iter, ity, flat) ← if fs.any isExcl then do
            let (filtE, arr, ety) ← exclIter c1 fs more bd flatOverride
            let bindX ← coerce gp ⟨lg.value, lg.vty⟩ ty
            let one ← fresh .void
            let iter := Expr.forE one (.lit (.arr #[.tup []])) (.seq (.assign xs bindX) filtE) arr
            pure (Expr.prim .flatten [← inferable ⟨iter, .arr (.arr ety)⟩], ety, true)
          else do
            let (filt, c2) ← elabFilters c1 fs
            let bindX ← coerce gp ⟨lg.value, lg.vty⟩ ty
            let inner ← build c2 more bd (flatOverride := flatOverride)
            let one ← fresh .void
            pure (Expr.forE one (.lit (.arr #[.tup []])) (.seq (.assign xs bindX) filt) inner.e,
              inner.ty, more.isEmpty)
        -- (the steps in rounds, each a `forE` over a range twice as long as
        -- the last one's, whose body runs a step and gives the values of
        -- its iteration, if it came to a value: so the values are collected
        -- in linear time and space, where adding each to an array would copy
        -- it each time)
        let acc ← fresh (.arr ity)
        let size ← fresh .int
        let done ← fresh .logic
        let d ← fresh .int
        let vd : Expr := .lit .void
        let none : Expr := .lit Value.emptyArray
        let r ← fresh (.arr ity)
        -- (#283) a value that comes to a continuation member's choice point
        -- breaks out of the iteration, keeping what it did, with `bnd` set:
        -- it has no values of its own; any other break goes on
        let taken : Expr := match lg.bnd with
          | some b => .seq (.assign b (.lit (.logic false))) (.seq (.assign r none)
              (.seq (.loop (.seq (.assign r iter) (.seq (.assign b (.lit (.logic true))) Expr.brkV)))
                (.ite (.prim .query [.local b]) (.seq lg.after (.local r)) (.seq .brk (.prim .userErr [])))))
          | none => .seq (.assign r iter) (.seq lg.after (.local r))
        let stepBody : Expr := .ite (p2 .eq (.local lg.sp) (.lit (.int 0)))
          (.seq (.assign done (.lit (.logic true))) none)
          (.seq lg.step (.ite (.prim .query [.local lg.has]) taken none))
        let round : Expr := .forE d (p2 .range (.lit (.int 1)) (.local size))
          (p2 .eq (.local done) (.lit (.logic false))) stepBody
        let body : Expr := .seq (.assign acc (p2 .concat (.local acc) (.prim .flatten [round])))
          (.ite (p2 .eq (.local done) (.lit (.logic true))) Expr.brkV
            (.seq (.assign size (p2 .mul (.local size) (.lit (.int 2)))) vd))
        -- A nested continuation's failed outcome breaks the nearest loop.
        -- This producer catches that break before the private outcome loop,
        -- so forward it before any enclosing generator can run another item.
        let values := match c.forOutcomeSlot with
          | some flag => Expr.ite (.prim .query [.local flag]) (.local acc)
              (.seq .brk (.prim .userErr []))
          | none => Expr.local acc
        -- A source break has already run its lexical cleanup. Every lazy
        -- loop crossed must forward it without exposing accumulated values.
        let values := match c.forBreakSlot with
          | some flag => forwardSourceBreak flag values
          | none => values
        let code : Expr := .seq lg.init (.seq (.assign acc none) (.seq (.assign size (.lit (.int 16)))
          (.seq (.assign done (.lit (.logic false))) (.seq (.loop body) values))))
        if flat then return ⟨code, .arr ity⟩
        match ity with
        | .arr t => return ⟨.prim .flatten [code], .arr t⟩
        | _ => eerr gp "internal: nested for"
      -- the source: evaluated before the iterations; a failing source gives no iterations
      let (slot, src, c1, pre) ← match g with
        | .decl gp n none false (.range _ lo hi) => do
          let es ← elabInts { c with canFail := true, inTaking := true } gp [lo, hi]
          let (slot, c1) ← declare c n .int
          pure (slot, Expr.prim .range es, c1, Expr.lit (.logic true))
        | .gen gp x idx srcE => do
          let rs ← elabE { c with canFail := true, inTaking := true } srcE none
          match rs.ty with
          | .map kt vt =>
            -- `for (V : M)` and `for (K -> V : M)`: over the (key, value) pairs
            let tmp ← fresh rs.ty
            let src := if (rs.e.mayFail ctx.sigProg) then
                Expr.orE tmp rs.e (.lit Value.emptyArray) else rs.e
            let tp ← fresh (.tup [kt, vt])
            let (pre, c1) ← match idx with
              | none => do
                let (xs, c1) ← declare c x vt
                pure (Expr.assign xs (.prim (.tupGet 1) [.local tp]), c1)
              | some i => do
                let (is, c1) ← declare c i kt
                let (xs, c2) ← declare c1 x vt
                pure (Expr.seq (.assign is (.prim (.tupGet 0) [.local tp]))
                  (.assign xs (.prim (.tupGet 1) [.local tp])), c2)
            pure (tp, src, c1, pre)
          | _ =>
          match idx with
          | some i => do
            -- `I -> X : A`: iterate over the indices of A
            let ty ← match rs.ty with
              | .arr t => pure t
              | t => eerr gp s!"a for generator needs an array, string or map, found {t.show}"
            let tmp ← fresh rs.ty
            let src0 := if (rs.e.mayFail ctx.sigProg) then
                Expr.orE tmp rs.e (.lit Value.emptyArray) else rs.e
            let ta ← fresh rs.ty
            let (islot, c1) ← declare c i .int
            let (xslot, c2) ← declare c1 x ty
            let src := Expr.seq (.assign ta src0)
              (.prim .range [.lit (.int 0), p2 .sub (.prim .len [.local ta]) (.lit (.int 1))])
            pure (islot, src, c2, Expr.assign xslot (p2 .index (.local ta) (.local islot)))
          | none => do
          let ty ← match rs.ty with
            | .arr t => pure t
            | t => eerr gp s!"a for generator needs an array, string or map, found {t.show}"
          let tmp ← fresh rs.ty
          let src := if (rs.e.mayFail ctx.sigProg) then
              Expr.orE tmp rs.e (.lit Value.emptyArray) else rs.e
          let (slot, c1) ← declare c x ty
          pure (slot, src, c1, Expr.lit (.logic true))
        | .decl gp n _ false _ => do
          -- `X := a₁ | … | aₙ` (#208): over the alternatives' indices, each
          -- alternative bound in the filter (so a failing one is skipped)
          let some b := Choice.binding? g | eerr g.pos "bad for clause"
          -- (an `if` with choices in its branches picks its branch first, once, #235)
          let (pre, ty, es, _) ← match b.branchy with
            | some i => elabBranchAlts { c with canFail := true, inTaking := true } gp i b.ty b.place
            | none => do let (ty, es) ← elabAlts { c with canFail := true } gp b; pure (none, ty, es, false)
          checkNewLocal c gp n
          let k ← fresh .int
          let (xs, c1) ← declare c n ty
          let idx := Expr.lit (.arr (choiceIdx es.length))
          pure (k, (pre.map (Expr.seq · idx)).getD idx, c1, Expr.assign xs (Expr.altE k es))
        | _ => eerr g.pos "bad for clause"
      -- (an exclusive choice among the filters, #314: its paths in this
      -- iteration's filter, so that a failure in one rolls back to this
      -- generator, as the `if` it stands for would)
      if fs.any isExcl then
        let (filtE, arr, ety) ← exclIter c1 fs more bd flatOverride
        let filt := match pre with
          | .lit _ => filtE
          | e => .seq e filtE
        if peel then return ⟨.seq filt arr, .arr ety⟩
        return ⟨.prim .flatten [← inferable ⟨Expr.forE slot src filt arr, .arr (.arr ety)⟩], .arr ety⟩
      let (filt, c2) ← elabFilters c1 fs
      let filt := if fs.isEmpty then pre else
        match pre with
        | .lit _ => filt
        | e => .seq e filt
      let inner ← build c2 more bd (flatOverride := flatOverride)
      let loopE := Expr.forE slot src filt inner.e
      match more with
      | [] => return ⟨loopE, .arr inner.ty⟩
      | _ =>
        match inner.ty with
        | .arr t => return ⟨.prim .flatten [← inferable ⟨loopE, .arr inner.ty⟩], .arr t⟩
        | _ => eerr p "internal: nested for"
  match pre with
  | [] =>
    let r ← build ctx gs body
    if firstDecides && gs.isEmpty then return ⟨.prim .mkArr [r.e], .arr r.ty⟩
    return r
  | _ =>
    -- (an exclusive choice among them, #314: its paths in this filter)
    -- (through a generator over one element, whose filters they are)
    if pre.any isExcl then
      -- (named for the depth too: a for of an alternative's, inside this
      -- one's clauses, has the same position)
      -- (a continuation's, #335: its filter, then its values, failing where
      -- the filter fails, as the caller's filter would with it copied in)
      return ← build ctx ((.gen p s!"$u{p.line}_{p.col}_{ctx.locals.length}" none (.arrayLit p [.tuple p []]), pre) :: gs) body false
        (peel := firstDecides)
    -- filters before any generator: iterate once over a one-element array
    let (filt, c1) ← elabFilters ctx pre
    let slot ← fresh .void
    let inner ← build c1 gs body
    match gs with
    | [] =>
      if firstDecides then return ⟨.seq filt (.prim .mkArr [inner.e]), .arr inner.ty⟩
      return ⟨.forE slot (.lit (.arr #[.tup []])) filt inner.e, .arr inner.ty⟩
    | _ =>
      match inner.ty with
      | .arr t =>
        if firstDecides then return ⟨.seq filt inner.e, .arr t⟩
        let iter := Expr.forE slot (.lit (.arr #[.tup []])) filt inner.e
        return ⟨.prim .flatten [← inferable ⟨iter, .arr inner.ty⟩], .arr t⟩
      | _ => eerr p "internal: nested for"

end OpenVerse.Front
