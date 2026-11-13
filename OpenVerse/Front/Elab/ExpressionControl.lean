/- A contiguous expression-handler stage; fallthrough preserves source pattern order. -/
import OpenVerse.Front.Elab.Control

namespace OpenVerse.Front
open OpenVerse
set_option maxHeartbeats 800000 in
partial def elabExprControlWith
    (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabStmt : Ctx → SExpr → Option Ty → EM (R × Ctx))
    (elabDefers : Ctx → List (SExpr × List Local) → EM Expr)
    (elabRefineExit : Ctx → Pos → List SExpr → List SExpr → EM R)
    (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx))
    (elabRefinedIf : Ctx → Pos → Pos → String → String → SExpr → SExpr → Option SExpr → Option Ty → (made : optParam Bool false) → (ifType : optParam Bool false) → EM (Option R))
    (elabSet : Ctx → Pos → SExpr → Option String → SExpr → EM R)
    (elabFor : Ctx → Pos → List SExpr → SExpr → (prepared : optParam Bool false) → (firstDecides : optParam Bool false) → (failure : optParam (Option SExpr) none) → EM R)
    (elabOneClauses : Ctx → List SExpr → EM (R × Ctx))
    (elabCase : Ctx → Pos → SExpr → List (Option SExpr × SExpr) → Option Ty → EM R)
    (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  match se with
  | e@(.ite _ [.decl _ _ none false (.app _ (.ident _ "$methodCast") _ false)] _ (some _)) =>
    elabE ctx (pruneMethodCases ctx e) exp
  | e@(.ite _ [.decl _ _ none false (.app _ (.ident _ "$methodCase") _ false)] _ (some _)) =>
    elabE ctx (pruneMethodCases ctx e) exp
  | .ite p conds0 thenE elseE =>
    -- (a first clause the elaborator made, whose branch is its own too)
    let (madeCast, conds) := Refine.unmade conds0
    -- (#243, #351) a cast as a later clause of the condition, `if (c₁, …,
    -- D := T[X], rest) then B else E`, that only a failure context's clause
    -- may be (one that refines type arguments, opens them, or goes through a
    -- view): as written first, and when that is refused for it, as `if (c₁,
    -- …) then (if (D := T[X], rest) then B else E) else E`, when the clauses
    -- before it have nothing its failure would undo (they print nothing,
    -- change no object, and call nothing, which might), else with the cast
    -- taking the rest as its branch in a clause of its own, `B` casting
    -- again (`withCastClauses`)
    -- (as written for this `if` only: not the `if`s in it, nor those the
    -- cast's own path makes, #400's review)
    let asWritten := ctx.asWritten
    let ctx := { ctx with asWritten := false }
    -- (with no expected type, one with a cast that refines as clause `k` and
    -- an `else`: any `if`'s type, `ifBranches`, the branch, the clauses
    -- after the cast and `thenE`, typed under the refinement, as
    -- `elabRefinedIf` finds it, the clauses before it as they are; nothing
    -- is kept, so that every elaboration decides the same)
    let refinedIfTy (k : Nat) (ee : SExpr) : EM (Option (Ty × Bool)) := do
      let st ← get
      let some (dp, d, T, x) := conds[k]?.bind Refine.castClause? | return none
      let τ? ← tryCatch (do
          let c ← if k == 0 then pure ctx else
            pure (← elabSeq { ctx with canFail := true, inTaking := true, typeOnly := true } (conds.take k) none).2
          let branch := Refine.castRest p (conds.drop (k + 1)) thenE (some (Refine.noValue p))
          let r? ← elabRefinedIf { c with canFail := ctx.canFail, inTaking := ctx.inTaking, typeOnly := true }
            p dp d T x branch (some ee) none (made := true) (ifType := true)
          pure (r?.map fun r => (r.ty, match r.e with | .lit (.logic true) => true | _ => false))) fun _ => pure none
      set st
      return τ?
    let nested (k : Nat) (_ : String) : EM (Option R) := do
      let castC := conds[k]!
      let st0 ← get
      -- (the clauses before it, apart: what they would leave behind)
      let pre := conds.take k
      let fx0 := (← get).fx
      let n0 := (← get).nslots
      modify fun s => { s with fx := [] }
      -- (ones that take a choice's values, which this cannot elaborate apart,
      -- the cast's clause of its own takes too: `withCastClauses`)
      let some (rp, _) ← tryCatch (some <$> elabSeq { ctx with canFail := true, inTaking := true, asWritten := true } pre none)
          fun _ => do set st0; pure none
        | return none
      let fxP := (← get).fx
      set st0
      modify fun s => { s with fx := fx0 }
      -- (and a `var` set there, a slot they do not bind, which the
      -- failure would restore, #400's review)
      if rp.e.printsOrCalls || fxP.any (·.1 == "writes") || rp.e.assignsBelow n0 then return none
      -- (the cast's branch is the elaborator's, not the source's: so a
      -- clause after it, always, `true?`, which the lift then carries,
      -- `made`)
      -- (`true?`, which may fail, keeps them a condition when they
      -- cannot fail themselves, as the whole condition could, as
      -- `Refine.castRest` does)
      let tq := SExpr.query p (.ident p "true")
      let innerC := castC :: conds.drop (k + 1) ++ [tq]
      match elseE with
      | none => return some (← elabE ctx (.ite p (pre ++ [tq]) (.ite p innerC thenE none) none) exp)
      | some ee =>
        -- (the `else` once, outside the clauses' names, #400's review:
        -- the branch gives an option of its value, or `true` for a
        -- `void` `if`, `false` when a clause fails, as #286's)
        -- (`thenE`'s value bound at `at?`: the `if`'s type, when the rule
        -- takes the branch at it, `refinedIfTy`; else at its own)
        let attempt (τ : Ty) (at? : Option STy := none) : EM R := do
          let isVoid := τ == .void
          let v := s!"$lc{p.line}_{p.col}"
          let thenV : SExpr := if isVoid then .block p [thenE, .ident p "true"]
            else .block p [.decl p v at? false thenE, .optionLit p (.ident p v)]
          let outer := SExpr.ite p (pre ++ [tq]) (.ite p innerC thenV (some (.ident p "false")))
            (some (.ident p "false"))
          let rty : Ty := if isVoid then .logic else .opt τ
          let r ← elabE ctx outer (some rty)
          let t ← fresh rty
          if isVoid then
            let eE ← elabE ctx ee none
            return ⟨.seq (.assign t r.e) (.ite (.prim .query [.local t]) (.lit .void) (.seq (← inferable eE) (.lit .void))), .void⟩
          let eE ← coerce p (← elabE ctx ee (some τ)) τ
          let xv ← fresh τ
          return ⟨.seq (.assign t r.e) (.ite (.assign xv (.prim .query [.local t])) (.local xv) eE), τ⟩
        match exp with
        | some τ => return some (← attempt τ)
        | none =>
          if let some (τ, atType) ← refinedIfTy k ee then
            return some (← attempt τ (if atType then some τ.toSTy else none))
          let st1 ← get
          let re ← elabE ctx ee none
          set st1
          if re.ty == .void then return some (← attempt .void)
          return some (← tryCatch (attempt re.ty) fun _ => do set st1; attempt .void)
    -- (and in a failure context, the branches, which are in it too: a cast
    -- in one that is an expression makes it the block of it)
    let branches : List (SExpr × (SExpr → EM R)) := if !ctx.canFail then [] else
      (thenE, fun b => elabE ctx (.ite p conds0 b elseE) exp) ::
        elseE.toList.map fun ee => (ee, fun b => elabE ctx (.ite p conds0 thenE (some b)) exp)
    if !asWritten then
      if let some r ← withCastClauses ctx conds thenE (fun _ => false)
          (elabE { ctx with asWritten := true } (.ite p conds0 thenE elseE) exp)
          (fun conds thenE => elabE ctx (.ite p conds thenE elseE) exp) (later := true) (alone := nested)
          (blocks := branches) then
        return r
    -- (a cast that refines type arguments, as the whole condition, #243,
    -- or as its first clause, the cast having no effects to undo when the
    -- rest fails: `if (D := T[X], rest) then B` is `if (D := T[X]) then (if
    -- (rest) then B)`, and with an `else E`, the branch's function gives
    -- `option{B}`, or `false` when the rest fails, and `E` runs once, in the
    -- caller, not under the refinement, #286)
    if let some (dp, d, T, x) := conds.head?.bind Refine.castClause? then
      let more := conds.drop 1
      match more, elseE with
      | [], _ =>
        match ← elabRefinedIf ctx p dp d T x thenE elseE exp (made := madeCast) with
        | some r => return r
        | none => pure ()
      | _, none =>
        match ← elabRefinedIf ctx p dp d T x (Refine.castRest p more thenE none) none exp (made := true) with
        | some r => return r
        | none => pure ()
      | _, some ee =>
        -- (at the if's type `τ`: void, the branch's function says whether
        -- the rest succeeded)
        -- (the branch runs outside any failure context, in the branch's
        -- function and in the caller, which keeps its result first: when
        -- it fails, the if fails, as a branch does; only `false`, the rest
        -- having failed, runs `E`)
        let v := s!"$cv{p.line}_{p.col}"
        let innerOf (τ : Ty) (at? : Option STy := none) : SExpr :=
          let thenV : SExpr := if τ == .void then .block p [thenE, .ident p "true"]
            else .block p [.decl p v at? false thenE, .optionLit p (.ident p v)]
          Refine.castRest p more thenV (some (.ident p "false"))
        let rtyOf (τ : Ty) : Ty := if τ == .void then .logic else .opt τ
        let attempt (τ : Ty) (at? : Option STy := none) : EM (Option R) := do
          let isVoid := τ == .void
          let inner := innerOf τ at?
          let rty : Ty := rtyOf τ
          match ← elabRefinedIf ctx p dp d T x inner (some (.ident p "false")) (some rty) (made := true) with
          | some r =>
            let t ← fresh rty
            if isVoid then
              let eE ← elabE ctx ee none
              return some ⟨.seq (.assign t r.e) (.ite (.prim .query [.local t]) (.lit .void) (.seq (← inferable eE) (.lit .void))), .void⟩
            let eE ← coerce p (← elabE ctx ee (some τ)) τ
            let xv ← fresh τ
            return some ⟨.seq (.assign t r.e) (.ite (.assign xv (.prim .query [.local t])) (.local xv) eE), τ⟩
          | none => return none
        -- (without an expected type: any `if`'s, `refinedIfTy`; when that
        -- cannot be found, the else's, else void, as a statement whose
        -- branches' types differ, a later elaboration deciding as the first
        -- did: by the result type of the function it asked for, `logic` for
        -- void)
        let r? ← match exp with
          | some t => attempt t
          | none => do
            match ← refinedIfTy 0 ee with
            | some (τ, atType) => attempt τ (if atType then some τ.toSTy else none)
            | none =>
              let st0 ← get
              let re ← elabE ctx ee none
              set st0
              -- (in a source context, the lift's tag depends on its type)
              let asked (τ : Ty) := ctx.types.castRequests.find? (·.key ==
                Refine.keyOf p d (refineTagOf ctx x (innerOf τ) (some (.ident p "false")) (some (rtyOf τ))))
              match (asked .void).orElse fun _ => asked re.ty with
              | some l => attempt (match l.ret with | .name "logic" => .void | _ => re.ty)
              | none =>
                if re.ty == .void then attempt .void
                else tryCatch (attempt re.ty) fun _ => attempt .void
        if let some r := r? then return r
    let (rc, ctxT) ← if Choice.hasChoice conds (choiceOrder ctx) then elabOneClauses { ctx with canFail := true } conds
      else elabSeq { ctx with canFail := true, inTaking := true } conds none
    -- (not while a function value is asked for, #214, #231: a call through
    -- it may fail once its class is made, in the elaboration that follows;
    -- likewise for the families of methods' uses, #283: `failabilityKnown`)
    if !(rc.e.mayFail ctx.sigProg) && (← ctx.failabilityKnown) then
      eerr p "the condition of this if cannot fail (Verse requires a failable condition)"
    let thenCtx := { ctxT with canFail := ctx.canFail, inTaking := ctx.inTaking }
    match elseE with
    | none =>
      let rt ← elabE thenCtx thenE (some .void)
      return ⟨.ite rc.e (← coerce p rt .void) (.lit .void), .void⟩
    | some ee =>
      ifBranches p exp ctx.retries (fun k e => elabE { thenCtx with retries := k } thenE e)
        (fun k e => elabE { ctx with retries := k } ee e)
        fun rt re ty => return ⟨.ite rc.e (← coerce p rt ty) (← coerce p re ty), ty⟩
  | .forE p clauses body => do
    -- (#243, #351) a clause that casts as only a failure context's clause
    -- may: as written, else with the rest of its clauses as one block
    let asWritten := ctx.asWritten
    let ctx := { ctx with asWritten := false }
    if !asWritten then
      -- (a choice, all of whose values a `for` takes, is a generator)
      let isGen : SExpr → Bool
        | .gen .. | .decl _ _ none false (.range ..) => true
        | c => Choice.hasChoice [c] (choiceOrder ctx)
      -- (the body, which casts again, at the element type expected, when
      -- one is: the type the refinement must give its value)
      let typed (b : SExpr) : SExpr := match exp with
        | some (.arr t) =>
          let v := s!"$forValue{p.line}_{p.col}"
          .block b.pos [.decl b.pos v (some t.toSTy) false b, .ident b.pos v]
        | _ => b
      if let some r ← withCastClauses ctx clauses body isGen (elabE { ctx with asWritten := true } se exp)
          (fun clauses body => elabE ctx (.forE p clauses (typed body)) exp) then
        return r
    let returns := (Refine.findPart (fun | .ret .. => true | _ => false) false (.block p (clauses ++ [body]))).isSome
    let breaks := (ctx.inLoop || ctx.refineExits.brk.isSome) &&
      (Refine.findPart Refine.isBreak true (.block p clauses)).isSome
    let ownBreak ← if ctx.inLoop && breaks && ctx.forBreakSlot.isNone then
        some <$> fresh .logic
      else pure none
    let ctx := { ctx with
      forOutcomeSlot := none,
      forBreakSlot := ownBreak.orElse fun _ => if ctx.inLoop then ctx.forBreakSlot else none }
    let withExits : EM (R × Bool) := do
      let sourceRet ← match ctx.refineExits.ret with
        | some (some (_, t), _) => resolveTy ctx.types p t
        | some (none, _) => pure .void
        | none => match ctx.forReturnSlot.bind ctx.lookup with
          | some { ty := .opt t, .. } => pure t
          | _ => pure ctx.retTy
      -- (named by its place, which is the same in every function the
      -- consumer is elaborated in, the source, a trial and each
      -- continuation's, whose keys name it, `contKey`; and by the locals in
      -- scope only should one of the same place be in scope already)
      let place := s!"$forReturn{p.line}_{p.col}" ++ (if p.file.isEmpty then "" else s!"_{p.file}")
      let name := if (ctx.lookup place).isSome then s!"{place}_{ctx.locals.length}" else place
      let slot ← fresh (.opt sourceRet)
      let breakName := name ++ "$break"
      let breaking ← if breaks then some <$> fresh .logic else pure none
      let storage (n : String) : Option SourceStorage := if ctx.suspends then
        some { frame := ctx.frameName, name := n, args := ctx.frameArgs } else none
      let returnLocal : Local := { name, slot, ty := .opt sourceRet, mutable := true, storage := storage name }
      let breakLocal := breaking.map fun slot =>
        ({ name := breakName, slot, ty := .logic, mutable := true, storage := storage breakName } : Local)
      let extra := returnLocal :: breakLocal.toList
      modify fun st => { st with frameSlots := st.frameSlots ++ extra.filterMap (fun l => l.storage.map (l.slot, ·)) }
      let c := { ctx with locals := extra ++ ctx.locals }
      let flag ← fresh .logic
      let metadata := SExpr.set p (.ident p name) none (.ident p name)
      let metadata := if breaking.isSome then .block p [metadata, .set p (.ident p breakName) none (.ident p breakName)] else metadata
      let body := SExpr.app p (.ident p "$forReturns")
        [metadata, .ident p (if ctx.canFail then "true" else "false"), body] false
      let before ← get
      let r ← elabFor { c with forOutcomeSlot := some flag } p clauses body
      -- Only the consumer moves into a filter-bound continuation. Source
      -- cleanup and the final return remain in the suspending caller.
      let afterConsumer ← get
      let waits := forContWaits ctx before afterConsumer [r.e] && before.forStageUses == afterConsumer.forStageUses
      let result ← fresh (.opt r.ty)
      let value ← fresh r.ty
      let returning := s!"{name}$value"
      -- Break-only consumers can occur in a defer, branch or constructor,
      -- whose lexical checks must never see an invented source return.
      let ret ← if returns then
          elabE c (.ite p [.decl p returning none false (.query p (.ident p name))]
            (.ret p (some (.ident p returning))) none) (some .void)
        else pure ⟨.lit .void, .void⟩
      let failed := if ctx.canFail then Expr.prim .fail [] else .prim .userErr []
      let normal := Expr.ite (.assign value (.prim .query [.local result])) (.local value) failed
      let leaving := Expr.seq ret.e normal
      let leaving ← if breaking.isSome then do
          let stop ← elabE c (.ite p [.query p (.ident p breakName)] (Refine.liftedBreak p) none) (some .void)
          pure (Expr.seq stop.e leaving)
        else pure leaving
      let (run, after) ← if ctx.inLoop then do
          let escaped ← fresh .logic
          pure (Expr.seq (.assign escaped (.lit (.logic false))) (forwardForBreaks flag escaped r.e),
            Expr.ite (.prim .query [.local escaped]) .brk (.lit .void))
        else pure (r.e, Expr.lit .void)
      let code := Expr.seq (.assign slot (.lit .none))
        (.seq (.assign flag (.lit (.logic true)))
          (.seq (.assign result (.lit .none))
            (.seq (.loop (.seq (.assign result (.prim .mkSome [run])) Expr.brkV))
              (.seq after leaving))))
      let code := (breaking.map fun slot => Expr.seq (.assign slot (.lit (.logic false))) code).getD code
      return (⟨code, r.ty⟩, waits)
    let elaborate : EM R := do
      if !breaks && !returns then
        return ← elabFor ctx p clauses body
      if !ctx.suspends then return (← withExits).1
      -- Immediate consumers and staged waiting consumers carry source exits.
      -- Other waiting consumers retain their original source-return lowering.
      let st0 ← get
      if let some (r, waits) ← tryCatch (some <$> withExits) (fun _ => pure none) then
        if !waits then return r
      set st0
      elabFor ctx p clauses body
    let r ← elaborate
    return ⟨ownBreak.map (fun flag => Expr.seq (.assign flag (.lit (.logic false))) r.e) |>.getD r.e, r.ty⟩
  | .gen p _ _ _ => eerr p "a generator X : source can only appear in a for clause"
  | .loop _ body =>
    let lctx := { ctx with
      inLoop := true, inRepeat := true, loopDefers := ctx.defers.length,
      loopRollback := ctx.canFail || ctx.inRollback,
      inChoice := false, forBreakSlot := none, forBreakCapture := none,
      refineExits := { ctx.refineExits with brk := none } }
    let r ← elabE lctx body none
    return ⟨.loop (← inferable r), .void⟩
  | .brk p =>
    if ctx.inChoice then
      eerr p "internal: a break in first-success clauses that do not forward one (#283)"
    if !ctx.inLoop then
      eerr p (if ctx.inDefer then "break is only allowed inside loop (not for), and cannot leave a defer: block"
              else "break is only allowed inside loop (not for)")
    if let some name := ctx.forBreakCapture then
      let some target := ctx.lookup name | eerr p "internal: missing for break slot"
      if target.ty != .logic then eerr p "internal: invalid for break type"
      let ds ← elabDefers (ctx.exitDefers ctx.loopRollback) ctx.defers
      let some pack := ctx.forExitPacket | eerr p "internal: missing for break outcome"
      let out ← elabE { ctx with defers := [] } pack (some ctx.retTy)
      return ⟨.seq ds (.seq (.assign target.slot (.lit (.logic true))) (.ret out.e)), .never⟩
    -- the defers of the scopes it leaves, inside its loop
    let ds ← elabDefers (ctx.exitDefers ctx.loopRollback) (ctx.defers.take (ctx.defers.length - ctx.loopDefers))
    let jump := ctx.forBreakSlot.map (fun flag => Expr.seq (.assign flag (.lit (.logic true))) .brk) |>.getD .brk
    return ⟨.seq ds jump, .never⟩
  | .ret p e? =>
    if ctx.inParamDefault then eerr p "return is not allowed in a parameter's default"
    if ctx.inDefer then eerr p "return is not allowed in a defer: block"
    if ctx.inCtor then eerr p "return is not allowed in a constructor (it would skip the items after it)"
    if ctx.inBlock then eerr p "return is not allowed in a block: clause (it would skip the clauses after it)"
    if ctx.inBranch then eerr p "return is not allowed in a branch (Book of Verse ch. 14)"
    if let some (binding, pack) := ctx.refineExits.ret then
      let pre ← match binding, e? with
        | some (n, t), some e => pure [SExpr.decl p n (some t) false e]
        | some (_, t), none => eerr p s!"return needs a value of type {(← resolveTy ctx.types p t).show}"
        | none, some e => pure [e]
        | none, none => pure []
      return ← elabRefineExit { ctx with loopRollback := false } p pre pack
    -- Refining lifts above forward their return first. Here we are back
    -- in the owning continuation: save the operand before local cleanup,
    -- then return its abort packet with the latest mutable copy-outs.
    if let some name := ctx.forReturnSlot then
      let some target := ctx.lookup name | eerr p "internal: missing for return slot"
      let .opt ty := target.ty | eerr p "internal: invalid for return type"
      let value ← match e? with
        | some e => coerce p (← elabE ctx e (some ty)) ty
        | none =>
          if ty != .void then eerr p s!"return needs a value of type {ty.show}"
          pure (.lit .void)
      let saved ← fresh ty
      let ds ← elabDefers (ctx.exitDefers false) ctx.defers
      let some pack := ctx.forExitPacket | eerr p "internal: missing for return outcome"
      let out ← elabE { ctx with defers := [] } pack (some ctx.retTy)
      return ⟨.seq (.assign saved value) (.seq ds
        (.seq (.assign target.slot (.prim .mkSome [.local saved])) (.ret out.e))), .never⟩
    let some e := e?
      | do
        if ctx.retTy != .void then eerr p s!"return needs a value of type {ctx.retTy.show}"
        return ⟨.seq (← elabDefers (ctx.exitDefers false) ctx.defers) (.ret (.lit .void)), .never⟩
    let r ← elabE ctx e (some ctx.retTy)
    let v ← coerce p r ctx.retTy
    if ctx.defers.isEmpty then return ⟨.ret v, .never⟩
    -- the value first, then the defers of every scope it leaves
    let t ← fresh ctx.retTy
    return ⟨.seq (.assign t v) (.seq (← elabDefers (ctx.exitDefers false) ctx.defers) (.ret (.local t))), .never⟩
  | .caseE p scrut arms => elabCase ctx p scrut arms exp
  | .decl p _ _ _ _ =>
    let (r, _) ← elabStmt ctx se exp
    let _ := p
    return r
  | .set p lhs op rhs => elabSet ctx p lhs op rhs
  | _ => eerr se.pos "internal: expression routed to the wrong elaboration stage"

end OpenVerse.Front
