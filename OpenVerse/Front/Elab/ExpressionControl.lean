/- A contiguous expression-handler stage; fallthrough preserves source pattern order. -/
import OpenVerse.Front.Elab.Control

namespace OpenVerse.Front
open OpenVerse

/-- A `return` of a value other than the empty value in a function whose
    result is `void`, which discards it: a warning, the Book of Verse's 2002
    (`FlowControl/Return.versetest:179`, "explicitly returning a non-void
    value from a function with a void return type produces a warning"; its
    `return F()` of a `void` `F` gives none). -/
def warnVoidReturn (p : Pos) (result value : Ty) : EM Unit := do
  if result == .void && value != .void && value != .never && !value.isUnit then
    warnAt p s!"this return gives a value of type {value.show}, which a function whose result is void discards"

/-- A successful ordinary collector whose values only read its source world
    needs no selected-world replay. Calls, writes and exits retain recovery. -/
private partial def stableRefinementReads (ctx : Ctx) (e : SExpr) : Bool :=
  let allowed := match e with
    | .int .. | .char .. | .char32 .. | .float ..
    | .member .. | .query .. | .neg .. | .notE ..
    | .cmp .. | .andE .. | .orE .. | .tuple .. | .block ..
    | .arrayLit .. | .optionLit .. | .logicLit .. | .ite .. => true
    | .str _ parts => parts.all fun | .text _ => true | _ => false
    | .ident _ name => (ctx.lookup name).isSome || !(ctx.sig? name).any (·.isConst)
    | .decl _ _ _ false _ => true
    | .app _ (.ident _ name) _ true =>
      ctx.types.classes.contains name && (ctx.lookup name).isNone && (ctx.sig? name).isNone
    | .app _ (.ident _ name) _ false => ["$choice", "$excl", "$alt", "$group"].contains name
    | _ => false
  allowed && e.children.all (stableRefinementReads ctx)

private def stableRefinementCollector (ctx : Ctx) (clauses : List SExpr) (body : SExpr) : Bool :=
  -- Local declarations and implicit members can shadow a class identifier;
  -- only the unshadowed checked class-cast application is a stable read.
  -- Accessor dispatch can turn even a name or index into an effectful call;
  -- keep full recovery whenever any accessor is available.
  ctx.types.accessors.isEmpty && ctx.selfClass.isNone &&
    !(Choice.localDecls (.block body.pos (clauses ++ [body]))).any (fun (name, _) =>
      ctx.types.classes.contains name) &&
    clauses.all (stableRefinementReads ctx) && stableRefinementReads ctx body

set_option maxHeartbeats 800000 in
partial def elabExprControlWith
    (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabStmt : Ctx → SExpr → Option Ty → EM (R × Ctx))
    (elabDefers : Ctx → List (SExpr × List Local) → EM Expr)
    (elabRefineExit : Ctx → Pos → List SExpr → List SExpr → EM R)
    (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx))
    (elabRefinedIf : Ctx → Pos → Pos → String → String → SExpr → SExpr → Option SExpr → Option Ty → (made : optParam Bool false) → EM (Option R))
    (refinedIfType : Ctx → Pos → String → String → SExpr → SExpr → SExpr → EM (Option (Ty × Bool)))
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
    if !ctx.refinementTransportActive && hasRefinementClauses ctx conds0 then
      let saved ← get
      if !saved.refiningHintProbe then
        return ← tryCatch (elabE { ctx with refinementTransportActive := true } se exp) fun original => do
          if !refinementRecoveryError original then throw original
          let failed ← get
          set { saved with refiningHintProbe := true }
          let expected ← match exp, elseE with
            | some ty, _ => pure (some ty)
            | none, none => pure (some Ty.void)
            | none, some otherwise =>
              tryCatch (do
                let thenTy ← refinementPrefixTypeWith elabE elabOneClauses ctx conds0 thenE
                let elseTy := (← elabE { ctx with typeOnly := true } otherwise none).ty
                pure (joinTy ctx.types thenTy elseTy none)) (fun _ => pure none)
          set saved
          let some expected := expected.filter (!·.hasNever) | do set failed; throw original
          tryCatch (elabRefinementIfAt elabE { ctx with refinementTransportActive := true }
            p conds0 thenE elseE expected) fun _ => do
              set failed
              throw original
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
    -- after the cast and `thenE`, typed under the refinement
    -- (`refinedIfType`), the clauses before it as they are; nothing
    -- is kept, so that every elaboration decides the same. `none` when the
    -- clause is no cast that refines: an index or a call, `D := F[X]`, looks
    -- the same (`Refine.castClause?`), and so does a cast of no type
    -- arguments. When the rule gives the `if` no type, why not.)
    let refinedIfTy (k : Nat) (ee : SExpr) : EM (Option (Ty × Bool)) := do
      let st ← get
      let some (_, d, T, x) := conds[k]?.bind Refine.castClause? | return none
      let c ← if k == 0 then pure ctx else
        pure (← elabSeq { ctx with canFail := true, inTaking := true, typeOnly := true } (conds.take k) none).2
      let branch := Refine.castRest p (conds.drop (k + 1)) thenE (some (Refine.noValue p))
      let τ? ← refinedIfType { c with canFail := ctx.canFail, inTaking := ctx.inTaking, typeOnly := true } p d T x branch ee
      set st
      return τ?
    -- (at an expected type `τ`, `attempt`'s branch as it is, else, when
    -- that is refused, at `τ`, as an `if`'s branches are, `ifBranches`, and
    -- as with the cast alone: `false` for an option has no type of its own)
    let atExpected {α : Type} (τ : Ty) (attempt : Ty → Option STy → EM α) : EM α :=
      tryCatch (attempt τ none) fun err => tryCatch (attempt τ (some τ.toSTy)) fun _ => throw err
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
          elabE ctx outer (some rty)
        -- Only the selected branch can use the annotation retry. An error
        -- in the unchanged else must not repeat that entire suffix at
        -- every link of a refining conditional chain.
        let finish (τ : Ty) (r : R) : EM R := do
          let isVoid := τ == .void
          let rty : Ty := if isVoid then .logic else .opt τ
          let t ← fresh rty
          if isVoid then
            let eE ← elabE ctx ee none
            return ⟨.seq (.assign t r.e) (.ite (.prim .query [.local t]) (.lit .void) (← discardValue eE)), .void⟩
          let eE ← coerce p (← elabE ctx ee (some τ)) τ
          let xv ← fresh τ
          return ⟨.seq (.assign t r.e) (.ite (.assign xv (.prim .query [.local t])) (.local xv) eE), τ⟩
        match exp with
        | some τ =>
          let r ← atExpected τ fun τ at? => attempt τ at?
          return some (← finish τ r)
        | none =>
          let some (τ, atType) ← refinedIfTy k ee | return none
          let r ← attempt τ (if atType then some τ.toSTy else none)
          return some (← finish τ r)
    -- (and in a failure context, the branches, which are in it too: a cast
    -- in one that is an expression makes it the block of it)
    let branches : List (SExpr × (SExpr → EM R)) := if !ctx.canFail then [] else
      (thenE, fun b => elabE ctx (.ite p conds0 b elseE) exp) ::
        elseE.toList.map fun ee => (ee, fun b => elabE ctx (.ite p conds0 thenE (some b)) exp)
    if !asWritten then
      if let some r ← withCastClauses elabE elabOneClauses ctx conds thenE (fun _ => false)
          (elabE { ctx with asWritten := true } (.ite p conds0 thenE elseE) exp)
          (fun conds thenE => elabE ctx (.ite p conds thenE elseE) exp)
          (later := true) (alone := nested)
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
          let inner := innerOf τ at?
          let rty : Ty := rtyOf τ
          elabRefinedIf ctx p dp d T x inner (some (.ident p "false")) (some rty) (made := true)
        let finish (τ : Ty) (r : R) : EM R := do
          let t ← fresh (rtyOf τ)
          if τ == .void then
            let eE ← elabE ctx ee none
            return ⟨.seq (.assign t r.e) (.ite (.prim .query [.local t]) (.lit .void) (← discardValue eE)), .void⟩
          let eE ← coerce p (← elabE ctx ee (some τ)) τ
          let xv ← fresh τ
          return ⟨.seq (.assign t r.e) (.ite (.assign xv (.prim .query [.local t])) (.local xv) eE), τ⟩
        -- (without an expected type: any `if`'s, `refinedIfTy`; none for a
        -- clause that is no cast that refines, which the `if` takes as any)
        let r? : Option (Ty × R) ← match exp with
          | some t => do
            let r ← atExpected t fun τ at? => attempt τ at?
            pure (r.map (t, ·))
          | none => do
            match ← refinedIfTy 0 ee with
            | some (τ, atType) => do
              let r ← attempt τ (if atType then some τ.toSTy else none)
              pure (r.map (τ, ·))
            | none => pure none
        if let some (τ, r) := r? then return ← finish τ r
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
    -- An opening cast must retain the complete original world before
    -- ordinary clause replay moves its later snapshots into a lift.
    if !ctx.refinementTransportActive && clauses.any (fun clause =>
        (Refine.castClause? clause).any (fun (_, _, target, _) => ctx.types.classes.contains target) ||
        (refinementConditionalBinding? ctx clause).isSome) then
      let initial ← get
      if exp.isNone && !initial.refiningHintProbe &&
          clauses.any (fun clause => (refinementConditionalBinding? ctx clause).isSome) then
        -- Preserve ordinary inference, including its joins. Only a refused
        -- selected world needs a caller-world candidate from the fallback.
        return ← tryCatch (do
          let ordinary ← elabE { ctx with refinementTransportActive := true } se none
          let after ← get
          let deferred := after.pendingWaitingCasts > initial.pendingWaitingCasts ||
            !(after.needs.without initial.needs).casts.isEmpty ||
            (after.loopFirst.drop initial.loopFirst.length).any (fun use =>
              use.lift.toOption.any (fun helper => helper.name.startsWith "$contf"))
          let sourceRet ← tryCatch (some <$> resolveTy ctx.types p (firstReturnType ctx)) (fun _ => pure none)
          set after
          let returning := sourceRet.any (fun ty => !ty.params.isEmpty) &&
            (Refine.findPart (fun | .ret .. => true | _ => false) false body).isSome
          if !deferred || (ordinary.ty.params.isEmpty && !returning) ||
              stableRefinementCollector ctx clauses body then return ordinary
          let mut needsWorld := false
          set { after with refiningHintProbe := true }
          for clause in clauses do
            if let some (_, _, conditional) := refinementConditionalBinding? ctx clause then
              let openResult ← tryCatch (do
                let some (none, fallback) := (Choice.arms conditional).getLast? | pure true
                let result ← elabE { ctx with typeOnly := true } fallback none
                pure (!result.ty.params.isEmpty)) (fun _ => pure true)
              needsWorld := needsWorld || openResult
          set initial
          -- Its ordinary join is authoritative; never replace it with the
          -- fallback's narrower type during a deferred-world retry.
          let named ← tryCatch (some <$> resolveTy ctx.types p ordinary.ty.toSTy) (fun _ => pure none)
          set initial
          let some (.arr value) := named | do set after; return ordinary
          if !needsWorld || (value.hasNever && !(value == .never && returning)) then do
            set after
            return ordinary
          tryCatch (elabE { ctx with
            refinementTransportActive := true, refinementTransportValue := some value,
            asWritten := true } se none) (fun _ => do set after; pure ordinary)) fun original => do
          if !refinementRecoveryError original then throw original
          let failed ← get
          set { initial with refiningHintProbe := true }
          let ordinaryClauses := clauses.map fun clause =>
            match refinementConditionalBinding? ctx clause with
            | some (name, annotation, conditional) =>
              match (Choice.arms conditional).getLast? with
              | some (none, fallback) => .decl clause.pos name annotation false fallback
              | _ => clause
            | none => clause
          let candidate ← tryCatch (do
            let result ← elabE { ctx with typeOnly := true, refinementTransportActive := true }
              (.forE p ordinaryClauses body) none
            -- The saved caller environment must name the candidate: no
            -- nominal type or default placeholder created by the probe.
            let named ← resolveTy ctx.types p result.ty.toSTy
            pure (some named)) (fun _ => pure none)
          set initial
          let some (.arr value) := candidate | do set failed; throw original
          -- A return-only collector retains its actual bottom element.
          -- This supplies no invented type for a bottom-only initializer.
          let returnOnly := value == .never &&
            (Refine.findPart (fun | .ret .. => true | _ => false) false body).isSome
          if value.hasNever && !returnOnly then do set failed; throw original
          tryCatch (elabE { ctx with
            refinementTransportActive := true, refinementTransportValue := some value, asWritten := true } se none) fun _ => do
              set failed
              throw original
      if let some (.arr value) := exp then
        let saved ← get
        -- A supplied contextual type, including bottom components, is
        -- checked directly; the separate inference probe invents no type.
        if !saved.refiningHintProbe then
          return ← tryCatch (do
            let ordinary ← elabE { ctx with refinementTransportActive := true } se exp
            -- A producer can defer its suffix before the generated helper
            -- exposes the lost world. Validate the ordinary source first,
            -- then retain the world before that continuation is staged.
            let ordinaryState ← get
            let deferredSuffix := (ordinaryState.loopFirst.drop saved.loopFirst.length).any fun use =>
              use.lift.toOption.any (fun helper => helper.name.startsWith "$contf")
            let mut needsWorld := false
            if deferredSuffix || ordinaryState.pendingWaitingCasts > saved.pendingWaitingCasts ||
                !(ordinaryState.needs.without saved.needs).casts.isEmpty then
              -- A closed conditional value carries no caller-world index
              -- across its branch. Keep its successful ordinary lowering.
              set { ordinaryState with refiningHintProbe := true }
              for clause in clauses do
                if let some (_, _, conditional) := refinementConditionalBinding? ctx clause then
                  let openResult ← tryCatch (do
                    let some (none, fallback) := (Choice.arms conditional).getLast? | pure true
                    let result ← elabE { ctx with typeOnly := true } fallback none
                    pure (!result.ty.params.isEmpty)) (fun _ => pure true)
                  needsWorld := needsWorld || openResult
              set ordinaryState
            if needsWorld && !stableRefinementCollector ctx clauses body &&
                clauses.any (fun clause => (refinementConditionalBinding? ctx clause).isSome) then
              set saved
              tryCatch (elabE { ctx with
                refinementTransportActive := true, refinementTransportValue := some value, asWritten := true } se exp)
                (fun _ => do set ordinaryState; pure ordinary)
            else pure ordinary) fun original => do
            if !refinementRecoveryError original then throw original
            let failed ← get
            set saved
            tryCatch (elabE { ctx with
              refinementTransportActive := true, refinementTransportValue := some value
              asWritten := true } se exp) fun _ => do
                set failed
                throw original
    -- (#243, #351) a clause that casts as only a failure context's clause
    -- may: as written, else with the rest of its clauses as one block
    let asWritten := ctx.asWritten
    let ctx := { ctx with asWritten := false }
    if !asWritten then
      -- (a choice, all of whose values a `for` takes, is a generator)
      let isGen : SExpr → Bool
        | .gen .. | .decl _ _ _ false (.range ..) => true
        | c => Choice.hasChoice [c] (choiceOrder ctx)
      -- (the body, which casts again, at the element type expected, when
      -- one is: the type the refinement must give its value)
      let typed (b : SExpr) : SExpr := match exp with
        | some (.arr t) =>
          let v := s!"$forValue{p.line}_{p.col}"
          .block b.pos [.decl b.pos v (some t.toSTy) false b, .ident b.pos v]
        | _ => b
      if let some r ← withCastClauses elabE elabOneClauses ctx clauses body isGen (elabE { ctx with asWritten := true } se exp)
          (fun lifted liftedBody => do
            let saved ← get
            tryCatch (elabE ctx (.forE p lifted (typed liftedBody)) exp) fun original => do
              if ctx.refinementTransportActive || saved.refiningHintProbe || !refinementRecoveryError original then throw original
              let some (.arr value) := exp | throw original
              if value.hasNever then throw original
              set saved
              tryCatch (elabE { ctx with
                refinementTransportActive := true
                refinementTransportValue := some value, asWritten := true }
                (.forE p lifted (typed body)) exp) fun _ => do
                  set saved
                  throw original) then
        return r
    -- (a `return` in the body: none can be in the clauses, a failure
    -- context, nor can a `break`, `checkJumps`)
    let returns := (Refine.findPart (fun | .ret .. => true | _ => false) false body).isSome
    let ctx := { ctx with forOutcomeSlot := none }
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
      let storage : Option SourceStorage := if ctx.suspends then
        some { frame := ctx.frameName, name, args := ctx.frameArgs } else none
      let returnLocal : Local := { name, slot, ty := .opt sourceRet, mutable := true, storage }
      modify fun st => { st with frameSlots := st.frameSlots ++ (storage.map (slot, ·)).toList }
      let c := { ctx with locals := returnLocal :: ctx.locals }
      let flag ← fresh .logic
      let metadata := SExpr.set p (.ident p name) none (.ident p name)
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
      let ret ← elabE c (.ite p [.decl p returning none false (.query p (.ident p name))]
        (.ret p (some (.ident p returning))) none) (some .void)
      let failed := if ctx.canFail then Expr.prim .fail [] else .prim .userErr []
      let normal := Expr.ite (.assign value (.prim .query [.local result])) (.local value) failed
      let leaving := Expr.seq ret.e normal
      let (run, after) ← if ctx.inLoop && !r.e.brkSafe false then do
          let escaped ← fresh .logic
          let forwarded := forwardForBreaks flag escaped r.e
          -- Private outcome aborts leave the producer's own loop. Only an
          -- actual forwarded source break needs an exit of the outer loop;
          -- a dead guard here would hide that outer loop's bottom type.
          if (Suspend.assignsIn forwarded).contains escaped then
            pure (Expr.seq (.assign escaped (.lit (.logic false))) forwarded,
              Expr.ite (.prim .query [.local escaped]) .brk (.lit .void))
          else pure (r.e, Expr.lit .void)
        else pure (r.e, Expr.lit .void)
      let code := Expr.seq (.assign slot (.lit .none))
        (.seq (.assign flag (.lit (.logic true)))
          (.seq (.assign result (.lit .none))
            (.seq (.loop (.seq (.assign result (.prim .mkSome [run])) Expr.brkV))
              (.seq after leaving))))
      return (⟨code, r.ty⟩, waits)
    if !returns then
      return ← elabFor ctx p clauses body
    if !ctx.suspends then return (← withExits).1
    -- Immediate consumers and staged waiting consumers carry source exits.
    -- Other waiting consumers retain their original source-return lowering.
    let st0 ← get
    if let some (r, waits) ← tryCatch (some <$> withExits) (fun _ => pure none) then
      -- Explicit conditional transport owns a staged outcome protocol,
      -- including a waiting consumer. The legacy raw-body fallback would
      -- drop its source return cell and mistake the helper's result type
      -- for the source function's result.
      if !waits || (ctx.refinementTransportValue.isSome &&
          clauses.any (fun clause => (refinementConditionalBinding? ctx clause).isSome)) then return r
    set st0
    elabFor ctx p clauses body
  -- (the parser makes generators in for clauses, and in first's, which
  -- reach here)
  | .gen p _ _ _ => eerr p "a generator X : source in first is not supported yet: openverse takes generators in for clauses only"
  | .loop _ body =>
    -- (a loop's body is no failure context, also in a <decides> function:
    -- "`decides` is not allowed in `loop`", the Book's tests,
    -- SOL-4199-BreakFromIf.versetest:79, 3512)
    let lctx := { ctx with
      inLoop := true, inRepeat := true, loopDefers := ctx.defers.length,
      loopRollback := ctx.canFail || ctx.inRollback, canFail := false,
      inChoice := false, refineExits := { ctx.refineExits with brk := none } }
    let r ← elabE lctx body none
    let body ← inferable r
    let code := Expr.loop body
    -- Only a break belonging to this loop can give it a normal value.
    -- `brkSafe false` excludes one, allowing breaks in nested loops;
    -- `Eval.no_control` also excludes breaks escaping a called function.
    -- Core types a loop as void, so an unreachable Err gives its bottom
    -- type a representation that Core can check at every expected type.
    if body.brkSafe false then return ⟨.seq code (.prim .userErr []), .never⟩
    return ⟨code, .void⟩
  | .brk p =>
    if !ctx.inLoop then
      eerr p (if ctx.inDefer then "break is only allowed inside loop (not for), and cannot leave a defer: block"
              else "break is only allowed inside loop (not for)")
    -- the defers of the scopes it leaves, inside its loop (none of them a
    -- failure context's clauses: `checkJumps`)
    let ds ← elabDefers (ctx.exitDefers ctx.loopRollback) (ctx.defers.take (ctx.defers.length - ctx.loopDefers))
    return ⟨.seq ds .brk, .never⟩
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
        | some e => do
          let r ← elabE ctx e (some ty)
          -- A direct `do return` has no enclosing source statement to
          -- check the operand before it becomes an abort packet.
          if !ctx.canFail && (FailCapture.admissionBody r.e).mayFail ctx.sigProg then
            eerr e.pos "this expression can fail, but it is not in a failure context"
          warnVoidReturn p ty r.ty
          coerce p r ty
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
    warnVoidReturn p ctx.retTy r.ty
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
