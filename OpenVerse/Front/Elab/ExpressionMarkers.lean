/- A contiguous expression-handler stage; fallthrough preserves source pattern order. -/
import OpenVerse.Front.Elab.Control

namespace OpenVerse.Front
open OpenVerse
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
    (elabOneGo : Ctx → List SExpr → EM (Expr × Ctx))
    (next : Ctx → SExpr → Option Ty → EM R)
    (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  match se with
  | .app _ (.ident _ "$nofail") [e] false =>
    elabE { ctx with canFail := false, inRollback := ctx.inRollback || ctx.canFail, inBlock := true } e exp
  | .app p (.ident _ "$defer") _ _ => eerr p "defer: is a statement: it has no value"
  | .app p (.ident _ "$sync") arms false => elabConc ctx p true arms exp
  | .app p (.ident _ "$race") arms false => elabConc ctx p false arms exp
  | .app p (.ident _ "$rush") arms false => elabConc ctx p false arms exp true
  | .app p (.ident _ "$spawn") [body] false => elabSpawn ctx p body
  | .app p (.ident _ "$branch") [body] false => elabBranch ctx p body
  | .app p (.ident _ "$refineBreak") [] false =>
    if ctx.inChoice then
      eerr p "break cannot leave the clauses of a failure context that has a choice (an if condition, first{…}, option{…}, …) (#208)"
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
    | .arr (.arr t) => return ⟨.prim .flatten [r.e], .arr t⟩
    | .opt (.arr (.arr t)) =>
      let result ← fresh r.ty
      let slot ← fresh (.arr (.arr t))
      return ⟨.seq (.assign result r.e) (.ite (.assign slot (.prim .query [.local result]))
        (.prim .mkSome [.prim .flatten [.local slot]]) (.lit .none)), .opt (.arr t)⟩
    | _ => eerr p "internal: staged flatten values"
  | .app p (.ident _ "$forPrepare") [.str _ [.text base], .decl _ _ (some view) _ _, .block _ copyIds, .block _ borrowIds, .ident _ flat, .block _ clauses, body] false => do
    let some plan := ctx.types.loopRequests.findSome? (fun l => l.stagePlan.filter (·.base == base))
      | eerr p "internal: missing for prepare plan"
    let .struct _ args ← resolveTy ctx.types p view | eerr p "internal: for prepare view"
    let copyNames := forStageCopyNames copyIds
    let borrowNames := borrowIds.filterMap fun | .ident _ n => some n | _ => none
    let req ← match forStagePrefixOf ctx plan args p clauses body (flat == "true") copyNames borrowNames with
      | .ok req => pure req
      | .error why => eerr p s!"cannot prepare this refining for: {why} (#417)"
    if !ctx.types.loopRequests.any (·.key == req.key) then
      modify fun st => { st with loopFirst := st.loopFirst ++
        [{ g := "", pos := p, itemCode := .lit .void, argSet := none, lift := .ok req }] }
      let ty ← resolveTy ctx.types p req.ret
      return ⟨.prim .userErr [], ty⟩
    elabApp ctx p (.ident p req.name) req.args true exp
  | .app p (.ident _ "$forStage") [.str _ [.text base], .decl _ _ (some view) _ _, .block _ copyIds, .block _ borrowIds, .ident _ root, .ident _ flat, .block _ clauses, body] false => do
    let some plan := (ctx.forStage.filter (·.base == base)).orElse fun _ =>
        ctx.types.loopRequests.findSome? (fun l => l.stagePlan.filter (·.base == base))
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
    let some plan := ctx.types.loopRequests.findSome? (fun l => l.stagePlan.filter (·.base == base))
      | eerr p "internal: missing for resume plan"
    let slot ← fresh r.ty
    let source := s!"{base}$ready"
    let env := source ++ "$env"
    let packet := source ++ "$packet"
    let c := { ctx with forStage := none, locals := { name := source, slot, ty := r.ty, mutable := false } :: ctx.locals }
    let call := SExpr.app p (.member p (.ident p env) plan.method) [] false
    let body := if plan.copies.isEmpty then call else
      let get (j : Nat) := SExpr.app p (.ident p packet) [.int p (j : Int)] false
      SExpr.block p (.decl p packet none false call ::
        (copyNames.zipIdx.map fun (n, j) => .set p (.ident p n) none
          (.app p (.ident p "$refineCopyOut") [get (j + 1)] false)) ++ [get 0])
    let body := if plan.outcome then .app p (.ident p "$forOutcomeValues") [body] false else body
    -- Preparation never executes a real generator: each successful prefix
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
  | .app _ (.ident _ "$forClauseExits") [.set _ (.ident _ slot) none _, .set _ (.ident _ breaking) none _, .ident _ mode, body] false =>
    elabE { ctx with
      canFail := mode == "true", defers := [], forReturnSlot := some slot,
      forBreakCapture := some breaking, forBreakSlot := none, inLoop := true, loopDefers := 0,
      loopRollback := mode == "true" || ctx.inRollback } body exp
  -- (#283) a call of an overloaded function with several values, as
  -- written, in the elaboration for types: the overload it takes noted
  | .app _ (.ident _ "$ovPick") [.int _ id, .ident _ f, call] false =>
    elabE { ctx with ovPick := some (id.toNat, f) } call exp
  | .app p (.ident _ "$inlineOv") (.ident _ f :: _) false =>
    eerr p s!"a call of {Choice.shownFnName f}, which is overloaded and has several values, is supported in the body of a function or method only, for now (#283)"
  | .app p (.ident _ "$ovUnresolved") [.ident _ f] false =>
    eerr p s!"internal: which overload of {Choice.shownFnName f} this call takes (#283)"
  -- (#283, `Choice.bifToExcl`) a block as an `if`'s branch binding a name
  -- its condition binds
  | .app _ (.ident _ "$shadows") [.ident q n] false =>
    eerr q s!"'{n}' is already defined; Verse does not allow shadowing (use set {n} = … for a var)"
  | .app p (.ident _ "$inline") (.ident _ f :: _) false =>
    if ctx.inTaking then
      if ctx.liftWhy != "" then
        eerr p s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from {ctx.liftWhy}, for now (#283)"
      eerr p (s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from here, for now (#235): " ++
        "not from a defer:'s body, " ++
        "an alternative of a set's choice, the right of " ++
        "and or or, a range, or a block with a range of its own as a branch")
    eerr p (s!"{Choice.shownFnName f} has several values, so a call of it must be in a failure context that takes them: " ++
      "an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#235)")
  | .app p (.ident _ "$each") (.app _ (.ident _ fa) _ _ :: _) false =>
    -- (a call of a recursive function with several values, #235)
    let f := if fa.endsWith "$all" then String.ofList (fa.toList.take (fa.length - 4)) else fa
    if ctx.inTaking then
      if ctx.liftWhy != "" then
        eerr p s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from {ctx.liftWhy}, for now (#283)"
      eerr p (s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from here, for now (#235): " ++
        "not from a defer:'s body, " ++
        "an alternative of a set's choice, the right of " ++
        "and or or, a range, or a block with a range of its own as a branch")
    eerr p (s!"{Choice.shownFnName f} has several values, so a call of it must be in a failure context that takes them: " ++
      "an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#235)")
  | .app p (.ident _ "$loop") (.ident _ f :: _) false =>
    -- (a call of a recursive function with several values taken lazily, #246)
    if ctx.inTaking then
      if ctx.liftWhy != "" then
        eerr p s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from {ctx.liftWhy}, for now (#283)"
      eerr p (s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from here, for now (#235): " ++
        "not from a defer:'s body, " ++
        "an alternative of a set's choice, the right of " ++
        "and or or, a range, or a block with a range of its own as a branch")
    eerr p (s!"{Choice.shownFnName f} has several values, so a call of it must be in a failure context that takes them: " ++
      "an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#235)")
  | .app p (.ident _ "$choice") _ false =>
    if ctx.inTaking && ctx.liftWhy != "" then
      eerr p s!"a choice (a | b) cannot be lifted from {ctx.liftWhy}, for now (#283)"
    if ctx.inTaking then
      eerr p ("a choice (a | b) cannot be lifted from here, for now (#208): not from a defer:'s body, " ++
        "an alternative of a set's " ++
        "choice, the right of and or or, a range, or a block with a range of its own as a branch")
    eerr p ("a choice (a | b) has several values, so it must be in a failure context that takes them: " ++
      "an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#208)")
  | .app p (.ident _ "$callSingleton") [a] false =>
    -- Elaborate the operand once, then reuse its checked result for either
    -- the whole tuple or its singleton element. Failed conversions must not
    -- discard successful nested elaboration and repeat the operand tree.
    if let some (pt@(.tup [inner])) := exp then
      let r ← if ← argNeedsTypeWith elabE ctx a then
          tryCatch (elabE ctx a (some inner)) (fun _ => elabE ctx a (some pt))
        else tryCatch (elabE ctx a none) fun err => do
          -- A nested generic call can itself require the element context.
          -- Genuine producer errors propagate without a shape retry.
          let emptyType := ["the type of an empty array{} must be given", "the type of an empty map{} must be given"].any
            fun diagnostic => (err.splitOn diagnostic).length > 1
          if (err.splitOn "cannot infer").length ≤ 1 && !emptyType then
            throw err
          let missing := ((err.splitOn "cannot infer type parameter ")[1]?).map
            fun text => (text.splitOn " ").headD ""
          let memberName (g : String) := ctx.selfClass.any fun c =>
            ctx.hasMethod c g || ((ctx.types.methodOverloads.lookup g).getD []).any (ctx.hasMethod c ·) ||
            ((ctx.types.fields c).any (·.1 == g) && !builtins.contains g && !softBuiltins.contains g)
          let callSig (g : String) : Option Sig :=
            if memberName g then
              ctx.selfClass.bind fun c => (ctx.methodDecl? c g).bind fun owner => ctx.sig? s!"{owner}.{g}"
            else (ctx.sig? g).orElse fun _ => ctx.sig? s!"{g}$init"
          let resultContext (s : Sig) :=
            let owner := if s.hasReceiver then
                match s.params.head? with
                | some (.struct c _) => ((ctx.types.sparams.lookup c).getD []).map (·.1)
                | _ => []
              else []
            s.ret.params.any fun v => s.tparams.any (·.1 == v) && !owner.contains v
          let noHint (s : Sig) := !resultContext s || missing.any fun v =>
            s.tparams.any (·.1 == v) && !s.ret.params.contains v
          let fnValue : Ty → Bool := fun | .struct n _ => (FnValues.parseName n).isSome | _ => false
          let probeState ← get
          let typedField (receiver : SExpr) (method : String) : Bool :=
            match (elabE { ctx with typeOnly := true, callInstanceProbe := none } receiver none).run probeState with
            | .ok (⟨_, .struct c args⟩, _) =>
              let method := if method.startsWith "$spawnMethod:" then (method.drop 13).toString else method
              let (view, method) := if method.startsWith "(" then
                  match (method.drop 1).toString.splitOn ":)" with
                  | [owner, method] => (owner, method)
                  | _ => (c, method)
                else (c, method)
              (ctx.methodDecl? view method).isNone &&
                !(((ctx.types.methodOverloads.lookup method).getD []).any (ctx.hasMethod view ·)) &&
                (ctx.types.fields view (ctx.types.upArgs c args view)).any fun (n, t, _) => n == method && fnValue t
            | _ => false
          let fixedResult := match a with
            | .app _ (.ident _ g) _ _ =>
              match ctx.lookup g with
              | some binding => fnValue binding.ty
              | none =>
                let receiver := if (ctx.lookup "Self").isSome then "Self" else "$Self"
                (memberName g && typedField (.ident a.pos receiver) g) ||
                  (callSig g).any (fun s => !resultContext s)
            | .app _ (.member _ receiver method) _ _ => typedField receiver method
            | _ => false
          let noResultEvidence := Choice.anyE (fun
            | .app q (.ident _ g) _ _ =>
              err.startsWith s!"{q.show}:" && (ctx.lookup g).isNone &&
                (callSig g).any noHint
            | .app q (.member _ receiver method) _ _ =>
              if !err.startsWith s!"{q.show}:" &&
                  !Choice.anyE (fun e => err.startsWith s!"{e.pos.show}:") receiver then false else
              let cls : Except String (Option String) := match receiver with
                | .ident _ "(super:)" => .ok (ctx.selfClass.bind fun c => (ctx.types.info c).parent)
                | _ => match (elabE { ctx with typeOnly := true, callInstanceProbe := none } receiver none).run probeState with
                  | .ok (⟨_, .struct cls _⟩, _) => .ok (some cls)
                  | .error receiverError => .error receiverError
                  | _ => .ok none
              match cls with
              -- Receiver expressions never receive the method's result
              -- context. The same receiver error cannot be repaired by it.
              | .error receiverError => receiverError == err
              | .ok cls =>
                let method := if method.startsWith "$spawnMethod:" then (method.drop 13).toString else method
                let (cls, method) := if method.startsWith "(" then
                    match (method.drop 1).toString.splitOn ":)" with
                    | [owner, method] => (some owner, method)
                    | _ => (cls, method)
                  else (cls, method)
                (cls.bind fun c => (ctx.methodDecl? c method).bind fun owner => ctx.sig? s!"{owner}.{method}").any noHint
            | .app _ callee _ _ =>
              -- A returned callable is also elaborated independently of
              -- the expected result of invoking it.
              match (elabE { ctx with typeOnly := true, callInstanceProbe := none } callee none).run probeState with
              | .error calleeError => calleeError == err
              | _ => false
            | _ => false) a
          -- A result hint cannot supply an unrelated parameter of the
          -- failing producer. Retrying it at every enclosing singleton
          -- boundary would multiply the same unfixable inference failure.
          if fixedResult || noResultEvidence then throw err
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
  | .app p (.ident _ "$firstP") [.block _ items] false =>
    -- (#246) `first{…}` of clauses that are lifted already (a consumer's,
    -- taken into a lazily taken call's function of its own): not again,
    -- which would bind their lifted names a second time
    let (code, c1) ← elabOneGo { ctx with inLoop := false, inChoice := ctx.inLoop, inTaking := true, canFail := true }
      items.dropLast
    let c1 := { c1 with inLoop := ctx.inLoop, inChoice := ctx.inChoice, inTaking := ctx.inTaking, canFail := ctx.canFail }
    let rv ← elabE c1 (items.getLastD (.tuple p [])) exp
    return ⟨.seq (Expr.firstE code) rv.e, rv.ty⟩
  | .app p (.ident _ "$first") [.block bp items] false =>
    -- `first{…}` and `first(…){…}`: without a choice, a block
    if !Choice.hasChoice items.dropLast (choiceOrder ctx) then return ← elabE ctx (.block bp items) exp
    -- with one (#208): the first success of the clauses, then the value (or
    -- body), which sees their names
    if !ctx.canFail then
      eerr p "first{…} with a choice can fail, but it is not in a failure context (#208)"
    let (rc, c1) ← elabOneClauses ctx items.dropLast
    let rv ← elabE c1 (items.getLastD (.tuple p [])) exp
    return ⟨.seq rc.e rv.e, rv.ty⟩
  | _ => next ctx se exp

end OpenVerse.Front
