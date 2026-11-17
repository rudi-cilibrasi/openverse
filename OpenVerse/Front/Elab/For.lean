/- Elaboration for; public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.ProducerOperations
import OpenVerse.Front.Elab.RefinementEnvironments
import OpenVerse.Front.Elab.Calls

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

/-! ### What a `for` undoes (the Book of Verse's rule)

A `for`'s clauses are one search, depth first, over the product of its
generators' values: reaching the body commits what the search did since the
last success, a failure undoes back to the most recent choice point (the
element or alternative being tried), and the search's end undoes what it
did since the last success (`FlowControl/for.versetest` 317-392,
`Range.versetest` 140, 159; docs/DESIGN.md, "What a `for` undoes"). Nested
`forE`s keep what a source, a range's bounds or the clauses before the next
generator did, so they are that search only when none of those can do
anything that undoing would change; otherwise the generators are levels of
the search below, one search step a failure context, and the bodies run
between the steps, outside every failure context. -/

/-- A search source is a sequence or an optional pair of saved range bounds. -/
private inductive ForDomain where
  | sequence (code : Expr) (ty : Ty) (retained : List Nat := [])
  | bounds (code : Expr)

private def ForDomain.code : ForDomain → Expr
  | .sequence code _ _ | .bounds code => code

private def ForDomain.ty : ForDomain → Ty
  | .sequence _ ty _ => ty
  | .bounds _ => .opt (.tup [.int, .int])

private def ForDomain.retained : ForDomain → List Nat
  | .sequence _ _ slots => slots
  | .bounds _ => []

/-- One generator of a `for` searched by the Book's rule: the slot of its
    element, its source, the code that binds the element's names and runs the
    filters after it, and the slots of the search: the source's value, the
    index of the element the search is at, whether that element is *active*
    (it went through the last success, so the levels below it may have more),
    and whether the level is resuming it in the current step. -/
structure ForLevel where
  slot : Nat
  src : Expr
  filt : Expr
  arr : Nat
  ix : Nat
  act : Nat
  res : Nat
  range : Option (Nat × Nat) := none
  /-- Source slots read by later steps, such as the array behind its indices. -/
  retained : List Nat := []

/-- Whether the `logic` in slot `s` is `true` (fails if not). -/
def isTrueIn (s : Nat) : Expr := p2 .eq (.local s) (.lit (.logic true))

private def ForLevel.enter (level : ForLevel) : Expr :=
  let clear := Expr.seq (.assign level.ix (.lit (.int (-1))))
    (.seq (.assign level.act (.lit (.logic false))) (.lit .void))
  let clear := match level.range with
    | none => clear
    | some (first, _) => .seq (.assign first (.lit (.logic true))) clear
  .seq (.assign level.arr level.src) clear

private def ForLevel.advance (level : ForLevel) (exhausted : Expr) : Expr :=
  let next := Expr.assign level.ix (p2 .add (.local level.ix) (.lit (.int 1)))
  let ready := Expr.lit .void
  match level.range with
  | none => .seq next
    (.ite (p2 .lt (.local level.ix) (.prim .len [.local level.arr])) ready exhausted)
  | some (first, bounds) =>
    let bound (i : Nat) := Expr.prim (.tupGet i) [.local bounds]
    .ite (.assign bounds (.prim .query [.local level.arr]))
      (.ite (isTrueIn first)
        (.seq (.assign first (.lit (.logic false))) (.seq (.assign level.ix (bound 0))
          (.ite (p2 .le (.local level.ix) (bound 1)) ready exhausted)))
        (.ite (p2 .lt (.local level.ix) (bound 1)) (.seq next ready) exhausted))
      exhausted

private def ForLevel.bindElement (level : ForLevel) : Expr :=
  .assign level.slot (if level.range.isSome then .local level.ix
    else p2 .index (.local level.arr) (.local level.ix))

private def newForLevel (slot : Nat) (domain : ForDomain) (filter : Expr) : EM ForLevel := do
  let range ← match domain with
    | .bounds _ => pure (some (← fresh .logic, ← fresh (.tup [.int, .int])))
    | .sequence .. => pure none
  return {
    slot, src := domain.code, filt := filter, arr := ← fresh domain.ty
    ix := ← fresh .int, act := ← fresh .logic, res := ← fresh .logic,
    range, retained := domain.retained }

/-- Preserve the traditional per-generator transaction boundaries while
    collecting a range's results in growing batches. -/
private def iterateForDomain (slot : Nat) (domain : ForDomain) (filter body : Expr)
    (bodyTy : Ty) : EM Expr := do
  let .bounds _ := domain | return .forE slot domain.code filter body
  let level ← newForLevel slot domain filter
  let done ← fresh .logic
  let size ← fresh .int
  let acc ← fresh (.arr bodyTy)
  let scratch ← fresh .int
  let empty := Expr.lit Value.emptyArray
  let datum := Expr.seq level.bindElement (.ite filter (.prim .mkArr [body]) empty)
  let exhausted := Expr.seq (.assign done (.lit (.logic true))) (.lit .void)
  let row := Expr.seq (level.advance exhausted)
    (.ite (isTrueIn done) empty datum)
  let batch := Expr.forE scratch (p2 .range (.lit (.int 1)) (.local size))
    (p2 .eq (.local done) (.lit (.logic false))) row
  let collect := Expr.seq (.assign acc (p2 .concat (.local acc) (.prim .flatten [batch])))
    (.ite (isTrueIn done) Expr.brkV (.seq
      (.assign size (p2 .mul (.local size) (.lit (.int 2)))) (.lit .void)))
  -- A break from a filter or body continues outward.
  let result := if filter.brkSafe false && body.brkSafe false then Expr.local acc
    else Expr.ite (isTrueIn done) (.local acc) (.seq .brk empty)
  return .seq level.enter (.seq (.assign done (.lit (.logic false)))
    (.seq (.assign size (.lit (.int 16))) (.seq (.assign acc empty)
      (.seq (.loop collect) result))))

/-- The code of one search step through the levels `ls` (the first entered
    already: its source's value in its slot, its index `-1`): it finds the next
    combination of their elements that passes every filter, setting `found`,
    or ends with `found` unset. Each level is a loop: an active element is
    resumed (its names stay bound, its code is not run again: the levels below
    are tried from where they are), any other is the next element, bound, its
    filters run and the level below entered; each try is a failure context of
    its own, which the levels below failing undo. The last level always moves
    to its next element (the active one went to the body). Every level's code
    is here once. -/
def ForLevel.step (found : Nat) : List ForLevel → Expr
  | [] => .seq (.assign found (.lit (.logic true))) (.lit .void)
  | [l] =>
    .loop (.seq (l.advance Expr.brkV)
      (.ite (.seq l.bindElement l.filt)
        (.seq (.assign found (.lit (.logic true))) Expr.brkV) (.lit .void)))
  | l :: next :: more =>
    .loop (.seq (.assign l.res (.local l.act)) (.seq (.assign l.act (.lit (.logic false)))
      (.seq (.ite (isTrueIn l.res) (.lit .void) (l.advance Expr.brkV))
        (.ite (.seq (.ite (isTrueIn l.res) (.lit .void) (.seq l.bindElement (.seq l.filt next.enter)))
              (.seq (ForLevel.step found (next :: more)) (isTrueIn found)))
          (.seq (.assign l.act (.lit (.logic true))) Expr.brkV) (.lit .void)))))

/-- Advance nested generators with the same boundaries as nested Core fors.
    A generator's filter commits before entering its child source. Exhausting
    that child therefore leaves the parent's successful work in place. -/
def ForLevel.stepNested (found : Nat) : List ForLevel → Expr
  | [] => ForLevel.step found []
  | [level] => ForLevel.step found [level]
  | level :: child :: rest =>
    let void := Expr.lit .void
    let enter := Expr.seq (level.advance Expr.brkV)
      (.ite (.seq level.bindElement level.filt)
        (.seq child.enter (.seq (.assign level.res (.lit (.logic true))) void)) void)
    .loop (.seq (.assign level.res (.local level.act))
      (.seq (.assign level.act (.lit (.logic false)))
        (.seq (.ite (isTrueIn level.res) void enter)
          (.seq (.ite (isTrueIn level.res) (ForLevel.stepNested found (child :: rest)) void)
            (.ite (isTrueIn found)
              (.seq (.assign level.act (.lit (.logic true))) Expr.brkV) void)))))

/-- The shared search code for a flat `for`. Its first successful step enters
    the first source and commits the prelude. Later steps advance the cursor. -/
structure ForSearch where
  head : ForLevel
  tail : List ForLevel
  prelude : Option Expr
  started : Nat
  found : Nat
  nested : Bool := false

def ForSearch.init (search : ForSearch) : Expr :=
  .assign search.started (.lit (.logic false))

def ForSearch.take (search : ForSearch) (row exhausted : Expr) : Expr :=
  let enter := match search.prelude with
    | some pre => Expr.seq pre search.head.enter
    | none => search.head.enter
  let step := Expr.seq (.assign search.found (.lit (.logic false)))
    (.seq (.ite (isTrueIn search.started) (.lit .void) enter)
      (.seq (ForLevel.step search.found (search.head :: search.tail)) (isTrueIn search.found)))
  .ite step (.seq (.assign search.started (.lit (.logic true))) row) exhausted

def ForSearch.takeNested (search : ForSearch) (row exhausted : Expr) : Expr :=
  let void := Expr.lit .void
  let enter := Expr.ite (isTrueIn search.started) void
    (.ite (search.prelude.getD void)
      (.seq search.head.enter (.seq (.assign search.started (.lit (.logic true))) void)) void)
  let step := Expr.ite (isTrueIn search.started)
    (ForLevel.stepNested search.found (search.head :: search.tail)) void
  .seq (.assign search.found (.lit (.logic false)))
    (.seq enter (.seq step (.ite (isTrueIn search.found) row exhausted)))

/-- Storage required to resume after a successful row. Clause bindings that
    remain live across the step are supplied by the caller. User cells stay
    in the surrounding invocation and are never copied by restoring this
    list. The final generator rebinds its element on every step. -/
def ForSearch.cursorSlots (search : ForSearch) (bindings : List Nat) : List Nat :=
  let rec levels : List ForLevel → List Nat
    | [] => []
    | level :: rest =>
      [level.arr, level.ix] ++ level.retained ++ level.range.toList.map (·.1) ++
        (if rest.isEmpty then [] else [level.act, level.slot]) ++ levels rest
  (search.started :: (levels (search.head :: search.tail) ++ bindings)).eraseDups

def ForSearch.capture (search : ForSearch) (bindings : List Nat) : EM R := do
  let slots := search.cursorSlots bindings
  let types := (← get).slotTys
  let columns ← slots.mapM fun slot =>
    match types[slot]? with
    | some ty => pure ty
    | none => throw s!"internal: missing type of for cursor slot {slot}"
  return ⟨.prim .mkTup (slots.map Expr.local), .tup columns⟩

def ForSearch.restore (search : ForSearch) (bindings : List Nat) (packet : Nat) (next : Expr) : Expr :=
  ((search.cursorSlots bindings).zipIdx).foldr (fun (slot, index) rest =>
    .seq (.assign slot (.prim (.tupGet index) [.local packet])) rest) next

/-- Return the next live row's cursor to the producer. An absent input
    starts a new search. A resumed input restores private slots before
    searching, without restoring enclosing mutable storage. Exhaustion is
    an absent result rather than a failing expression. -/
def ForSearch.takeFrom (search : ForSearch) (bindings : List Nat) (prior : Option Nat)
    (row : Option R := none) : EM R := do
  let cursor ← search.capture bindings
  let setup ← match prior with
    | none => pure search.init
    | some slot => do
      let packet ← fresh cursor.ty
      pure (.ite (.assign packet (.prim .query [.local slot]))
        (search.restore bindings packet (.lit .void)) (.seq search.init (.lit .void)))
  let payload := match row with
    | none => cursor
    | some row => ⟨.prim .mkTup [cursor.e, row.e], .tup [cursor.ty, row.ty]⟩
  let take := if search.nested then search.takeNested else search.take
  let result := take (.prim .mkSome [payload.e]) (.lit .none)
  return ⟨.seq setup result, .opt payload.ty⟩

structure ForCursorRequest where
  prior : SExpr
  outputs : List String

/-- One prepared alternative of a composed header, with its own cursor. -/
structure ForCursorArm where
  cursor : Ty
  row : Ty
  input : Nat
  next : Expr

def forCursorChoiceType (arms : List ForCursorArm) : Ty :=
  .tup [.int, .tup (arms.map (fun arm => .opt arm.cursor))]

/-- Resume the active alternative, then try later alternatives in source
    order. Evaluating a step and querying its option are separate, so effects
    committed by the alternative survive even when it has no rows. -/
def forCursorChoice (p : Pos) (prior : Option Nat) (arms : List ForCursorArm) : EM R := do
  let some first := arms.head? | eerr p "internal: a cursor choice without alternatives"
  unless arms.all (fun arm => arm.row == first.row) do
    eerr p "internal: composed cursor alternatives have different row types"
  let cursor := forCursorChoiceType arms
  let resultTy := Ty.opt (.tup [cursor, first.row])
  let previous ← fresh cursor
  let active ← fresh .int
  let kept ← fresh .logic
  let result ← fresh resultTy
  let void := Expr.lit .void
  let project (source : Expr) (index : Nat) := Expr.prim (.tupGet index) [source]
  let readPrior := match prior with
    | none => void
    | some input => .ite (.assign previous (.prim .query [.local input]))
      (.seq (.assign active (project (.local previous) 0)) void) void
  let mut steps := []
  for (arm, index) in arms.zipIdx do
    let packetTy := Ty.tup [arm.cursor, arm.row]
    let pending ← fresh (.opt packetTy)
    let accepted ← fresh packetTy
    let ordinal := Expr.lit (.int (Int.ofNat index))
    let input := Expr.ite (p2 .eq (.local active) ordinal)
      (project (project (.local previous) 1) index) (.lit .none)
    let state := Expr.prim .mkTup [ordinal, .prim .mkTup (arms.zipIdx.map fun (_, column) =>
      if column == index then .prim .mkSome [project (.local accepted) 0] else .lit .none)]
    let success := Expr.seq (.assign result (.prim .mkSome [.prim .mkTup [state, project (.local accepted) 1]]))
      (.seq (.assign kept (.lit (.logic true))) void)
    let attempt := Expr.seq (.assign arm.input input) (.seq (.assign pending arm.next)
      (.ite (.assign accepted (.prim .query [.local pending])) success void))
    let eligible := Expr.seq (p2 .eq (.local kept) (.lit (.logic false)))
      (p2 .le (.local active) ordinal)
    steps := steps ++ [.ite eligible attempt void]
  let start := [.assign active (.lit (.int (-1))), readPrior,
    .assign kept (.lit (.logic false)), .assign result (.lit .none)]
  return ⟨(start ++ steps).foldr Expr.seq (.local result), resultTy⟩

/-- Whether `e` can do something that undoing it would change: print, set an
    object's field, call a function (which may do either), or write a slot
    that `observable` names (a variable of the code around the `for`, or a
    `var` of its clauses). Conservative: allocating an object or binding a
    name of the clauses is not observable once undone. -/
partial def forClauseEffects (observable : Nat → Bool) : Expr → Bool
  | .lit _ | .local _ | .brk => false
  | .assign s e => observable s || forClauseEffects observable e
  | .print _ | .call .. => true
  | .heap (.set _) _ => true
  | .heap _ es | .prim _ es => es.any (forClauseEffects observable)
  | .seq a b => forClauseEffects observable a || forClauseEffects observable b
  | .ite c t e => forClauseEffects observable c || forClauseEffects observable t || forClauseEffects observable e
  | .forE _ it f b => forClauseEffects observable it || forClauseEffects observable f || forClauseEffects observable b
  | .loop e | .ret e => forClauseEffects observable e

/-- A call of a function with several values anywhere in `e`, as the
    functions are marked before their calls are lifted (`Choice.inlineCalls`:
    inlined, computed at the call, taken lazily, dispatched, or a point of a
    lazily taken group's own code). -/
partial def callsManyValued (e : SExpr) : Bool :=
  match e with
  | .app _ (.ident _ f) _ _ =>
    ["$inline", "$each", "$loop", "$dispatch", "$point"].contains f || e.children.any callsManyValued
  | _ => e.children.any callsManyValued

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
    (firstDecides : Bool := false) (failure : Option SExpr := none)
    (searchPrepared : Bool := false) (cursor : Option ForCursorRequest := none) : EM R := do
  let transport := ctx.refinementTransportValue
  if cursor.isSome && transport.isSome then
    eerr p "internal: refinement transport for resumable for headers"
  let ctx := { ctx with refinementTransportValue := none }
  if let some value := transport then
    let c := ctx
    -- Select the condition once, before searching its branch alternatives.
    -- Only the opaque owner crosses that condition boundary: the branch,
    -- later clauses and consumer retain the successful snapshot world.
    if let some index := clauses.findIdx? (fun clause => (refinementConditionalBinding? c clause).isSome) then
      let some (binding, annotation, conditional) := refinementConditionalBinding? c clauses[index]!
        | eerr p "internal: refinement conditional producer"
      let after := clauses.drop (index + 1)
      let outcome := (ctx.canFail && !firstDecides) || failure.isSome || forReturnBody? body
      let rec selected (expression : SExpr) (site : String) : SExpr :=
        let resume (conditions : List SExpr) (branch : SExpr) : SExpr × SExpr :=
          -- The selected world retains these locals, but their source names
          -- belong only to this condition and branch, not later clauses.
          let names := Choice.condDecls expression.pos conditions
          let ren := Choice.renamedFor (site ++ "$condition") (names.map (·.1))
          let conditions := Choice.declNames expression.pos names ++ conditions.map (Choice.renameE ren)
          let branch := Choice.renameE ren branch
          let ready := site ++ "$ready"
          let branchClause := SExpr.decl branch.pos binding annotation false branch
          -- Ordinary collectors prepare their raw suffix once in the
          -- selected world. Legacy first continuations already require
          -- prepared clauses; compact $loop/$each is not idempotent.
          let branchClauses := if !firstDecides then [branchClause] else
            Choice.prepare [branchClause] (choiceValues c) (choiceField c)
              (site := site ++ "$branch") (fieldOrder := choiceOrder c)
              (keepExcl := true) (keepBranches := choiceHasCast c)
          let suffix := branchClauses ++ after
          let prepare := refinementPrepareMarker c expression.pos value outcome
            (ctx.canFail || ctx.inRollback) conditions suffix body (forBody := true) (originalFor := !firstDecides)
          let consumer := forStageBodyAs body
            (.app expression.pos (.ident expression.pos "$refinementResume") [.ident expression.pos ready] false)
          (.decl expression.pos ready none false prepare, consumer)
        match expression with
        | .ite q conditions branch (some otherwise) =>
          let (prepare, consumer) := resume conditions branch
          .ite q [prepare] consumer (some (selected otherwise (site ++ "$else")))
        | branch =>
          let suffix := SExpr.forE expression.pos
            (SExpr.decl branch.pos binding annotation false branch :: after) body
          .app expression.pos (.ident expression.pos "$refinementContinue")
            [.decl expression.pos "$value" (some value.toSTy) false (.tuple expression.pos []), suffix] false
      let chosen := selected conditional s!"$refinementBranch{p.line}_{p.col}_{index}"
      let result := s!"$refinementBranchValues{p.line}_{p.col}_{index}"
      let consumer := forStageBodyAs body (SExpr.block p
        [.decl p result (some (Ty.arr value).toSTy) false chosen, .ident p result])
      -- An empty prefix contributes no collection layer in an ordinary
      -- for. The selected consumer already returns the complete array.
      if index == 0 && !firstDecides then
        return ← elabE c consumer (some (.arr value))
      let outer ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq c p
        (clauses.take index) consumer (prepared := prepared)
        (firstDecides := firstDecides) (failure := failure)
      let .arr (.arr resultType) := outer.ty | eerr p "internal: refinement conditional values"
      return ⟨← flattenValues outer, .arr resultType⟩
    if let some (before, filterPrefix, suffix) := refinementProducerParts c clauses then
      let name := s!"$refinementReady{p.line}_{p.col}_{c.locals.length}"
      let outcome := (ctx.canFail && !firstDecides) || failure.isSome || forReturnBody? body
      -- A return's abort packet is a protocol outcome, not a source
      -- failure context. Keep its original Signal/cleanup boundary.
      let sourceFailure := match body with
        | .app _ (.ident _ name) [_, .ident _ mode, _] false =>
          if name == "$forReturns" || name == "$forReturnBody" then mode == "true"
          else (ctx.canFail && !firstDecides) || failure.isSome
        | _ => (ctx.canFail && !firstDecides) || failure.isSome
      if refinementChainEligible c (before ++ filterPrefix ++ suffix) suffix then
        if let some owned ← refinementOwnedLocals c p clauses body then
          return ← elabE { c with refinementTransportValue := some value } owned (some (.arr value))
        let names := (Choice.localDecls (.block p clauses)).map (·.1) |>.eraseDups
        let written := SExpr.forE p clauses body
        let writtenSets := Choice.setsIn written
        let cells := names.filter fun name => writtenSets.contains name &&
          Choice.anyE (fun | .decl _ n (some _) true _ => n == name | _ => false) (.block p clauses)
        if !cells.isEmpty then
          if !c.types.classes.contains "$varcell" then
            askHelper p (refinementCellRequest p)
            return ⟨.prim .userErr [], .arr value⟩
          -- Use the existing typed cell transformation for clause-local
          -- variables shared by successive row owners. Caller variables
          -- keep the ordinary live copy-in/copy-out protocol.
          return ← elabE { c with refinementTransportValue := some value }
            (Choice.cellVars cells written) (some (.arr value))
        let code ← refinementChainOf c p filterPrefix suffix body value outcome
          (sourceFailure || ctx.inRollback)
        let some (chainClauses, chainBody) := code | return ⟨.prim .userErr [], .arr value⟩
        let r ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq c p
          (before ++ chainClauses) chainBody (prepared := true)
          (firstDecides := firstDecides) (failure := failure) (searchPrepared := true)
        let .arr (.arr t) := r.ty | eerr p "internal: refinement chain values"
        return ⟨← flattenValues r, .arr t⟩
      let prepare := refinementPrepareMarker c p value outcome (sourceFailure || ctx.inRollback)
        filterPrefix suffix body (forBody := true)
      let resume := SExpr.app p (.ident p "$refinementResume") [.ident p name] false
      let consumer := forStageBodyAs body resume
      -- One outer row prepares and resumes before the next row begins.
      -- Flatten only that row's returned values, never pre-collect Ready
      -- environments across generator iterations.
      let r ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq c p
        (before ++ [.decl p name none false prepare]) consumer
        (prepared := true) (firstDecides := firstDecides) (failure := failure)
      let .arr (.arr t) := r.ty | eerr p "internal: refinement consumer values"
      return ⟨← flattenValues r, .arr t⟩
  let stagePlan := ctx.forStage
  let bodyExpected := if firstDecides || stagePlan.isSome then none else transport
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
    | some { each := some (.app _ (.ident _ "$choiceProducer") _ false), .. } => [c]
    | some { pos := q, name := n, ty, each := some arr, .. } => Choice.genOver "" q n ty arr
    | _ => [c]
  let clauses := normGens clauses
  -- split into groups: [filters before the first generator], then (generator, filters)…
  let isBranch (c : SExpr) : Bool := (Choice.binding? c).any (·.branchy.isSome)
  let isGen : SExpr → Bool
    | .gen .. => true
    | .decl _ _ _ false (.range ..) => true
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
    canFail := bodyFail, inLoop := false, inRepeat := true,
    refineExits := { c.refineExits with brk := none },
    forExitPacket := failure.orElse fun _ => c.forExitPacket }
  -- elaborate the filters of one generator (in a failure context)
  let elabFilters (c : Ctx) (fs : List SExpr) : EM (Expr × Ctx) := do
    match fs with
    | [] => return (.lit (.logic true), c)
    | _ =>
      let (r, c') ← elabSeq { c with canFail := true, inTaking := true } fs none
      return (r.e, c')
  -- The ordinary composed/exclusive paths use the same handoff as a
  -- refining path. Probe a suffix once at its binding's common type;
  -- type-only probes recurse through these same shared suffixes.
  let stagedSuffix (c : Ctx) (q : Pos) (name : String) (bty : Ty)
      (alts rest : List SExpr) (bd : SExpr) (flat : Option Bool := none)
      (extraTops : List STop := []) (extraSources : List STop := []) (extraResumes : List Choice.ForResume := [])
      (immediate : Bool := false) :
      EM (Option (Choice.FirstLift × Choice.ForStagePlan × Ty × Bool)) := do
    let sourceFail := match bd with
      | .app _ (.ident _ f) [_, .ident _ mode, _] false =>
        if f == "$forReturns" || f == "$forReturnBody" then mode == "true" else bodyFail
      | _ => bodyFail
    if (stagePlan.isNone && ((!c.suspends && !immediate) || sourceFail)) ||
        c.inCtor || c.inBlock || c.inDefer then return none
    checkNewLocal c q name
    let before ← get
    let slot ← fresh bty
    let bound := { c with locals := { name, slot, ty := bty, mutable := false } :: c.locals }
    let required := if stagePlan.isSome then stageBorrows else []
    let written := SExpr.block q (rest ++ [bd] ++ required.map (SExpr.ident q ·))
    let caps := bound.capturesOf written
    let key := "stageOrdinary" ++ contKey bound q name (alts ++ rest ++ [bd]) ++
      forStageCaptureKey bound stageArgs caps
    let known := c.types.requests.loops.findSome? (fun l => l.stagePlan.filter (·.key == key))
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
    -- A synchronous suffix can use the existing direct continuation. A
    -- producer capability does not itself require a staged environment:
    -- forcing one serializes discovery of every later generator.
    if stagePlan.isNone && !waits && forBodySafe c bd then return none
    -- Refining lifts can infer their effects. Their initially empty fnFx
    -- is not an explicit computes restriction; retain the suffix's typed
    -- effects, as immediate continuations do, and expose them to a parent
    -- type-only probe as well.
    let allowed := heapFx.filter fun fx => c.fnFx.contains fx || effects.any (·.1 == fx) ||
      (stagePlan.orElse fun _ => known).any (·.specs.contains fx)
    let bound := { bound with fnFx := allowed }
    let request ← match forStagePlanOf bound q key rest bd value ((stagePlan.map (·.outcome)).getD bodyFail) required sourceSuspends
        (suspends := ((stagePlan.orElse fun _ => known).map (·.specs.contains "suspends")).getD c.suspends) with
      | .ok request => pure request
      | .error _ => return none
    let some plan := request.stagePlan | return none
    let args := plan.tparams.map fun tp =>
      (c.types.tvars.lookup tp.name).getD (.param tp.name (tp.constraint == "comparable"))
    let flatten := stagePlan.isSome && flat.getD stageFlat
    let prepare ← match forStagePrefixOf bound plan args q rest bd flatten (readyOnly := immediate) with
      | .ok prepare => pure prepare
      | .error _ => return none
    let prepare := { prepare with
      extraFns := prepare.extraFns ++ extraTops,
      sourceFns := prepare.sourceFns ++ extraSources,
      resumes := prepare.resumes ++ extraResumes }
    let environment ← if c.typeOnly || c.types.requests.loops.any (·.key == prepare.key) then pure [] else
      stagePrefixEnvironmentWith elabE bound q prepare plan
    let hasPlan := c.types.requests.loops.any (·.key == request.key)
    let hasPrefix := c.types.requests.loops.any (·.key == prepare.key)
    modify fun st => { st with
      fx := effects,
      pendingSourceSuspends := st.pendingSourceSuspends + (if sourceSuspends then 1 else 0) }
    noteFx q (heapFx.filter fun fx => (stagePlan.orElse fun _ => known).any (·.specs.contains fx))
      (some prepare.name)
    if !c.typeOnly then
      for req in (if hasPlan then [] else [request]) ++ (if hasPrefix then [] else [prepare]) ++
          environment.filter (fun req => !c.types.requests.loops.any (·.key == req.key)) do
        askHelper q req
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
  -- Declare `n`, a name a `for`'s clause at `q` binds.
  let declareAt (q : Pos) (c : Ctx) (n : String) (ty : Ty) : EM (Nat × Ctx) := do
    if c.lookup n |>.isSome then eerr q s!"'{n}' is already defined"
    let slot ← fresh ty
    return (slot, { c with locals := { name := n, slot, ty, mutable := false } :: c.locals })
  -- A generator over a range, an array, a map or a string, or a choice of
  -- alternatives that are values (#208): the slot of its element, its source
  -- (evaluated before its iterations; a failing source gives none), the
  -- source's type, the context with the names it binds, and the code that
  -- binds them from the element (a choice's alternative is evaluated there,
  -- so a failing one is skipped).
  let elabSource (c : Ctx) (g : SExpr) (stream : Bool) : EM (Nat × ForDomain × Ctx × Expr) := do
    match g with
    | .decl gp n ty false (.range _ lo hi) => do
      -- (a typed binding, `X:int := a..b`, Book of Verse tests,
      -- `FlowControl/for.versetest:17`, `Exercises/TwoSum.versetest:20`: its
      -- type is the range's, `int`)
      if let some t := ty then
        let rt ← resolveTy c.types gp t
        if rt != .int then
          let name := Choice.shownName n
          eerr gp s!"a range's values are ints: {name}:{rt.show} := a..b is not one; write {name}:int := a..b"
      let es ← elabInts { c with canFail := true, inTaking := true } gp [lo, hi]
      let (slot, c1) ← declareAt g.pos c n .int
      -- (a bound that fails gives no iterations, its effects and the
      -- other bound's rolled back, as a failing source does: Book of
      -- Verse ch. 7, "that iteration is skipped"; `for.versetest:317`)
      let domain ← if stream then do
        let bounds := Expr.prim .mkSome [.prim .mkTup es]
        if bounds.mayFail ctx.sigProg then
          pure (ForDomain.bounds (Expr.orE (← fresh (.opt (.tup [.int, .int]))) bounds (.lit .none)))
        else pure (ForDomain.bounds bounds)
      else do
        let src := Expr.prim .range es
        let src ← if src.mayFail ctx.sigProg then
          pure (Expr.orE (← fresh (.arr .int)) src (.lit Value.emptyArray))
        else pure src
        pure (ForDomain.sequence src (.arr .int))
      pure (slot, domain, c1, Expr.lit (.logic true))
    | .gen gp x idx srcE => do
      -- A lazy-return site's checking pass records the selected iterable
      -- type without inserting a binding or evaluating the source again.
      let (note, srcE) := match srcE with
        | .app _ (.ident _ "$noteLoopIterator") [.str _ [.text key], source] false =>
          (some key, source)
        | _ => (none, srcE)
      let rs ← elabE { c with canFail := true, inTaking := true } srcE none
      let rs ← elabContainerReceiverWith elabE c gp rs (fun
        | .arr _ | .map .. => true
        | _ => false) "iteration"
      if let some key := note then noteNeeds { nested := [(key, rs.ty.toSTy)] }
      -- (a weak map has none, Book of Verse ch. 3: "you cannot iterate over
      -- its entries", `weak_map.versetest:130`, 3524)
      if let .weakMap .. := rs.ty then eerr gp (weakMapNotIterated rs.ty)
      match rs.ty with
      | .map kt vt =>
        -- `for (V : M)` and `for (K -> V : M)`: over the (key, value) pairs
        let tmp ← fresh rs.ty
        let src := if (rs.e.mayFail ctx.sigProg) then
            Expr.orE tmp rs.e (.lit Value.emptyArray) else rs.e
        let tp ← fresh (.tup [kt, vt])
        let (pre, c1) ← match idx with
          | none => do
            let (xs, c1) ← declareAt g.pos c x vt
            pure (Expr.assign xs (.prim (.tupGet 1) [.local tp]), c1)
          | some i => do
            let (is, c1) ← declareAt g.pos c i kt
            let (xs, c2) ← declareAt g.pos c1 x vt
            pure (Expr.seq (.assign is (.prim (.tupGet 0) [.local tp]))
              (.assign xs (.prim (.tupGet 1) [.local tp])), c2)
        pure (tp, .sequence src rs.ty, c1, pre)
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
        let (islot, c1) ← declareAt g.pos c i .int
        let (xslot, c2) ← declareAt g.pos c1 x ty
        let src := Expr.seq (.assign ta src0)
          (.prim .range [.lit (.int 0), p2 .sub (.prim .len [.local ta]) (.lit (.int 1))])
        pure (islot, .sequence src (.arr .int) [ta], c2, Expr.assign xslot (p2 .index (.local ta) (.local islot)))
      | none => do
      let ty ← match rs.ty with
        | .arr t => pure t
        | t => eerr gp s!"a for generator needs an array, string or map, found {t.show}"
      let tmp ← fresh rs.ty
      let src := if (rs.e.mayFail ctx.sigProg) then
          Expr.orE tmp rs.e (.lit Value.emptyArray) else rs.e
      let (slot, c1) ← declareAt g.pos c x ty
      pure (slot, .sequence src rs.ty, c1, Expr.lit (.logic true))
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
      let (xs, c1) ← declareAt g.pos c n ty
      let idx := Expr.lit (.arr (choiceIdx es.length))
      pure (k, .sequence ((pre.map (Expr.seq · idx)).getD idx) (.arr .int), c1, Expr.assign xs (Expr.altE k es))
    | _ => eerr g.pos "bad for clause"
  -- (`peel`: the first group's filter, then its values, without the loop
  -- over its one element, for a continuation's clauses below)
  let rec build (c : Ctx) (gs : List (SExpr × List SExpr)) (bd : SExpr)
      (stageHere : Bool := true) (flatOverride : Option Bool := none) (peel : Bool := false) : EM R := do
    if let some plan := stagePlan.filter (fun _ => stageHere) then
      let clauses := gs.flatMap fun (g, fs) => g :: fs
      let (req, obj, ty) ← match forStageEnvOf { c with forStageArgs := stageArgs, forStageFlat := flatOverride.getD stageFlat, forStageCopies := stageCopies, forStageBorrows := stageBorrows } plan p clauses bd with
        | .ok r => pure r
        | .error why => eerr p s!"cannot stage this for: {why} (#417)"
      let r ← if c.types.requests.loops.any (·.key == req.key) then do
          -- Only this synthetic environment allocation is an implementation
          -- effect. Its fields are local reads, evaluated before allocation.
          let fx := (← get).fx
          let r ← elabE c obj (some ty)
          let e ← coerce p r ty
          modify fun st => { st with fx }
          pure (⟨e, ty⟩ : R)
        else do
          askHelper p req
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
            let req := cA.types.requests.loops.find? (·.key == key)
            if req.isNone && (contForLiftOf cA b.pos b.name ty .void [i] restCl bd bodyFail).toOption.isSome then
              -- Elaborate the suffix once, in its source context. Otherwise
              -- an inner lift can retain an outer var's old name after the
              -- enclosing lift has renamed it for mutable copy-out.
              let st0 ← get
              let slot ← fresh ty
              let cB := { cA.withTrial .continuation with locals := { name := b.name, slot, ty, mutable := false } :: cA.locals }
              let values ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
                cB p restCl bd (prepared := true) (firstDecides := true)
                  (failure := if bodyFail then some (.app p (.ident p "Err") [] false) else none)
              let .arr t := values.ty | eerr b.pos "internal: a refining for's suffix"
              if forContWaits cA st0 (← get) [values.e] then set st0 else
                match contForLiftOf cA b.pos b.name ty t [i] restCl bd bodyFail with
                | .ok lift =>
                  -- This body moves to an immediate helper, which discovers
                  -- its own locals and lifts: the trial asked for none of
                  -- them (`Ctx.keepsLifts`), only the continuations in it.
                  askHelper b.pos lift
                  return (codeA, .prim .userErr [], t)
                | .error why => eerr b.pos s!"cannot share the refining for's suffix: {why} (#417)"
            if let some l := req.filter cA.acceptsHelper then
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
            let rootCaptures := cA.capturesOf (.block p (i :: restCl ++ [bd]))
            let key := "stage" ++ contKey cA b.pos b.name (i :: restCl ++ [bd]) ++
              forStageCaptureKey cA [] (rootCaptures.filter (·.storage.isSome))
            let plan? := stagePlan.orElse fun _ =>
              cA.types.requests.loops.findSome? (fun l => l.stagePlan.filter (·.key == key))
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
              askHelper b.pos req
              modify fun st => { st with
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
            if !cA.types.requests.loops.any (·.key == nextReq.key) then
              askHelper b.pos nextReq
              return (codeA, .prim .userErr [], if stagePlan.isSome then Ty.struct plan.base rootArgs else resultTy)
            let some nextPlan := nextReq.stagePlan | eerr b.pos "internal: missing suffix plan"
            let nextArgs := nextPlan.tparams.map fun tp =>
              (cA.types.tvars.lookup tp.name).getD (.param tp.name (tp.constraint == "comparable"))
            let nextCopies := nextPlan.copies.map (·.1)
            let nextBorrows := nextPlan.borrowed
            let suffix ← match forStagePrefixOf suffixCtx nextPlan nextArgs b.pos restCl bd (stageOverride.getD stageFlat) nextCopies nextBorrows with
              | .ok req => pure req
              | .error why => eerr b.pos s!"cannot share this waiting for's suffix: {why} (#335, #417)"
            if !cA.types.requests.loops.any (·.key == suffix.key) then
              askHelper b.pos suffix
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
        let runPathIn (c : Ctx) (cl : List SExpr) (pb : SExpr) (flat : Bool) : EM (Expr × Expr × Ty) := do
          let transfer := if stagePlan.isSome && flat then some true else stageOverride
          let (f, a, t) ← exclIter c (cl.takeWhile (!isGen ·)) (groups (cl.dropWhile (!isGen ·))) pb transfer
          if !flat || stagePlan.isSome then return (f, a, t)
          match t with
          | .arr t' => return (f, ← flattenValues ⟨a, .arr t⟩, t')
          | _ => eerr gp "internal: a continuation's values"
        let runPath := runPathIn cA
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
        let req := if !contOK || cA.typeOnly || cA.types.requests.loops.isEmpty then none else
          let key := (if bodyFail then "fo" else "f") ++ contKey cA gp x (altsS ++ restCl ++ [bd])
          cA.types.requests.loops.find? (·.key == key)
        let kv := s!"$xk{gp.line}_{gp.col}{x}v"
        let plan : List (List SExpr × SExpr × Bool) ← if let some (prepare, plan, _, true) := staged then
            let (callCl, resumed) := forStageInvoke gp prepare plan.borrowed bd
            pure (alts.zipIdx.map fun ((gs, r), i) => (liftP gs r i ++ callCl, resumed, true))
          else match req with
          | some l =>
            if cA.acceptsHelper l then
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
                let (f0, a0, t0) ← runPathIn (cA.withTrial .continuation) (liftP gs0 r0 0 ++ restCl) bd false
                if forContWaits cA st0 (← get) [f0, a0] then set st0 else
                  match contForLiftOf cA gp x bty t0 altsS restCl bd bodyFail with
                  | .ok lift =>
                    askHelper gp lift
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
      let r ← elabE (bodyCtx c) bd bodyExpected
      -- The generated arrays must infer their element type during
      -- suspension lowering. As for array/tuple literals, a body that
      -- never completes has Core's void type without changing its exit.
      let r := if r.ty == .never then { r with e := .seq r.e (.lit .void) } else r
      if let some failed := failure then
        -- A body with no failure already returns explicit source-exit
        -- packets. Adding a conservative capture marker would invent a
        -- failure in a nonfailable resume method, even before lowering.
        if !r.e.mayFail ctx.sigProg then return r
        let packet ← elabE { c with canFail := false } failed (some c.retTy)
        let hint ← fresh (.opt r.ty)
        return ⟨FailCapture.marked hint r.e (.ret packet.e), r.ty⟩
      return r
    | (g, fs) :: more =>
      let declare := declareAt g.pos
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
          let forWIn (c : Ctx) (cl : List SExpr) (bd : SExpr) : EM R :=
            elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq c p cl bd
              (prepared := true) (failure := failure)
          let forW := forWIn bctx
          -- (#335, phase 2: another such choice, or an exclusive one, in the
          -- clauses after it, and a body that may run in a failure context:
          -- those clauses and the body a function of their own, which each
          -- alternative's for calls, instead of a copy in each)
          let restCl := fs ++ moreClauses
          do
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
                    (operations.rewriteSeq restCl) (operations.rewrite bd)
                    (extraTops := operations.extraFns) (extraSources := operations.sourceFns)
                    (extraResumes := operations.resumes) (immediate := !operations.sourceFns.isEmpty)
                  let after ← get
                  set { after with nslots := before.nslots, slotTys := before.slotTys }
                  if let some (prepare, plan, value, ready) := staged then
                    let joined := if polymorphic then choiceResultType c.types (typing.instances.map (value.subst ·)) else some value
                    if let some value := joined then
                      if !ready then return ⟨.prim .userErr [], .arr value⟩
                      let (callCl, resumed) := forStageInvoke gp prepare plan.borrowed bd
                        (copies := some (plan.copies.map (·.1)))
                      let mut parts : List R := []
                      for (a, i) in b.alts.zipIdx do
                        let r ← forW (liftA a i ++ (operations.casePrelude[i]?.getD []) ++ callCl) resumed
                        let r ← if polymorphic then do
                            let ty := Ty.arr (.arr value)
                            pure (⟨← coerce gp r ty, ty⟩ : R)
                          else pure r
                        let .arr (.arr t) := r.ty | eerr gp "internal: a staged continuation's values"
                        parts := parts ++ [⟨← flattenValues r, .arr t⟩]
                      let some first := parts.head? | eerr gp "internal: a choice without alternatives"
                      return ⟨parts.tail.foldl (fun acc r => p2 .concat acc r.e) first.e, first.ty⟩
          -- Failable bodies return outcomes so failure stops the entire
          -- for, rather than merely rejecting one continuation call.
          if forBodySafe c bd then
            let req := if c.typeOnly || c.types.requests.loops.isEmpty then none else
              let key := (if bodyFail then "fo" else "f") ++ contKey c gp b.name (b.alts ++ restCl ++ [bd])
              c.types.requests.loops.find? (·.key == key)
            if let some l := req then
              if c.acceptsHelper l then
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
                  | .arr (.arr t) => parts := parts ++ [⟨← flattenValues r, .arr t⟩]
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
                let r0 ← forWIn (bctx.withTrial .continuation) (liftA a0 0 ++ restCl) bd
                if forContWaits c st0 (← get) [r0.e] then set st0 else
                  match (do
                      let some bty := tys.head? | throw "no type"
                      let .arr vty := r0.ty | throw "no values"
                      contForLiftOf c gp b.name bty vty b.alts restCl bd bodyFail) with
                  | .ok lift =>
                    askHelper gp lift
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
                    bound p (operations.rewriteSeq restCl) (operations.rewrite bd) (prepared := true) (failure := failure)
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
                    (operations.rewriteSeq restCl) (operations.rewrite bd) bodyFail with
                    | .ok lift =>
                      let key := (if bodyFail then "fo" else "f") ++ contKey c gp b.name (b.alts ++ restCl ++ [bd])
                      joinedChoiceResult poly plan (operations.lift key lift)
                    | .error _ => return none
                  return some (lift, result, effects)) (fun _ => pure none)
                set before
                if let some (lift, result, effects) := trial then
                  askHelper gp lift
                  for (k, q, via) in effects do noteFx q [k] via
                  return ⟨.prim .userErr [], result⟩
                set st0
              else set st0
          let mut parts : List R := []
          for (a, i) in b.alts.zipIdx do
            if !c.hasCopiedOverloads (fs ++ moreClauses ++ [bd]) then
              parts := parts ++ [← forW (liftA a i ++ fs ++ moreClauses) bd]
              continue
            let scope := c.copiedOverloadKey gp b.name i
            -- The copy's discovery scope covers its producer and body too.
            -- Specialize all of them; otherwise an overload first discovered
            -- there could remain a single-value checking stub forever.
            let original := liftA a i ++ fs ++ moreClauses ++ [bd]
            let expanded ← match c.specializeCopiedOverloads scope original with
              | .ok code => pure code
              | .error why => eerr gp why
            let bound := Choice.boundIn expanded.dropLast
            let clauses := (original.dropLast.zip expanded.dropLast).zipIdx.flatMap fun ((before, after), j) =>
              if before == after then [after] else
                Choice.prepare [after] (fun n => choiceValues c n || bound.contains n) (choiceField c)
                  (fieldOrder := choiceOrder c) (site := s!"{site}copy{i}_{j}")
                  (keepExcl := true) (keepBranches := choiceHasCast c)
            let body := expanded.getLastD bd
            let sites := (clauses ++ [body]).flatMap Choice.copiedOverloadUses
            parts := parts ++ [← forWIn { bctx with copiedOverloadScope := scope, copiedOverloadSites := sites } clauses body]
          let some r0 := parts.head? | eerr gp "internal: a choice without alternatives"
          if let some r := parts.find? (·.ty != r0.ty) then
            eerr gp s!"the for's values have the type {r0.ty.show} for one alternative of this choice and {r.ty.show} for another"
          return ⟨parts.tail.foldl (fun acc r => p2 .concat acc r.e) r0.e, r0.ty⟩
      if let some producer := Choice.binding? g then
        if let some (.app _ (.ident _ "$choiceProducer")
            (value :: dictionary :: receiver :: arguments) false) := producer.each then
          let yieldTy ← producerYieldTypeWith elabE c producer.pos producer.ty value dictionary (arguments.length+1)
          let rest := fs ++ more.flatMap (fun (next, filters) => next :: filters)
          return ← elabProducerForWith elabE
            (fun c p clauses body prepared firstDecides failure =>
              elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
                c p clauses body prepared firstDecides failure)
            { c with canFail := ctx.canFail && !firstDecides }
            producer.pos producer.name yieldTy dictionary receiver arguments rest bd bodyFail
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
            pure (← flattenValues ⟨iter, .arr (.arr ety)⟩, ety, true)
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
        let empty : Expr := .lit Value.emptyArray
        let r ← fresh (.arr ity)
        -- (#283) a value that comes to a continuation member's choice point
        -- breaks out of the iteration, keeping what it did, with `bnd` set:
        -- it has no values of its own; any other break goes on
        let taken : Expr := match lg.bnd with
          | some b => .seq (.assign b (.lit (.logic false))) (.seq (.assign r empty)
              (.seq (.loop (.seq (.assign r iter) (.seq (.assign b (.lit (.logic true))) Expr.brkV)))
                (.ite (.prim .query [.local b]) (.seq lg.after (.local r)) (.seq .brk (.prim .userErr [])))))
          | none => .seq (.assign r iter) (.seq lg.after (.local r))
        let stepBody : Expr := .ite (p2 .eq (.local lg.sp) (.lit (.int 0)))
          (.seq (.assign done (.lit (.logic true))) empty)
          (.seq lg.step (.ite (.prim .query [.local lg.has]) taken empty))
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
        let code : Expr := .seq lg.init (.seq (.assign acc empty) (.seq (.assign size (.lit (.int 16)))
          (.seq (.assign done (.lit (.logic false))) (.seq (.loop body) values))))
        if flat then return ⟨code, .arr ity⟩
        match ity with
        | .arr t => return ⟨.prim .flatten [code], .arr t⟩
        | _ => eerr gp "internal: nested for"
      -- the source: evaluated before the iterations; a failing source gives no iterations
      let (slot, domain, c1, pre) ← elabSource c g (Choice.hasReturn bd)
      -- (an exclusive choice among the filters, #314: its paths in this
      -- iteration's filter, so that a failure in one rolls back to this
      -- generator, as the `if` it stands for would)
      if fs.any isExcl then
        let (filtE, arr, ety) ← exclIter c1 fs more bd flatOverride
        let filt := match pre with
          | .lit _ => filtE
          | e => .seq e filtE
        if peel then return ⟨.seq filt arr, .arr ety⟩
        return ⟨← flattenValues ⟨← iterateForDomain slot domain filt arr (.arr ety), .arr (.arr ety)⟩, .arr ety⟩
      let (filt, c2) ← elabFilters c1 fs
      let filt := if fs.isEmpty then pre else
        match pre with
        | .lit _ => filt
        | e => .seq e filt
      let inner ← build c2 more bd (flatOverride := flatOverride)
      let loopE ← iterateForDomain slot domain filt inner.e inner.ty
      match more with
      | [] => return ⟨loopE, .arr inner.ty⟩
      | _ =>
        match inner.ty with
        | .arr t => return ⟨← flattenValues ⟨loopE, .arr inner.ty⟩, .arr t⟩
        | _ => eerr p "internal: nested for"
  -- (A `for` whose generators are over ranges, arrays, maps, strings and
  -- choices of values, with no producer calls left after clause
  -- preparation and no exclusive choice: by the Book's rule, above. One
  -- whose clauses can do nothing that undoing would change before its last
  -- generator's elements is the nested `forE`s, as they are that search;
  -- another is the search. The others keep their lowerings below, which
  -- keep what a generator's clauses did: docs/DESIGN.md says which.)
  let plainGen (g : SExpr) : Bool := match g with
    | .gen .. => true
    | .decl _ _ _ false (.range ..) => true
    | c => match Choice.binding? c with
      | some b => !b.composed && b.branchy.isNone && b.each.isNone
      | none => false
  if let (some request, [], (g, fs) :: more) := (cursor, pre, gs) then
    if let some binding := Choice.binding? g then
      if binding.composed then
        let suffix := fs ++ more.flatMap fun (next, filters) => next :: filters
        let step (c : Ctx) (alt : SExpr) (index : Nat) (prior : SExpr) : EM R :=
          let clauses := Choice.prepare [.decl binding.pos binding.name binding.ty false alt]
            (choiceValues ctx) (choiceField ctx) (fieldOrder := choiceOrder ctx)
            (site := s!"$cursor{p.line}_{p.col}_{index}") (keepExcl := true) (keepBranches := choiceHasCast ctx)
          elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
            c p (clauses ++ suffix) body (prepared := true) (cursor := some { request with prior })
        let saved ← get
        let shapes ← binding.alts.zipIdx.mapM fun (alt, index) => do
          let probe ← step { ctx with typeOnly := true } alt index (.ident p "false")
          let .opt (.tup [state, row]) := probe.ty | eerr p "internal: malformed composed cursor arm"
          pure (state, row)
        restoreConstructProbe ctx saved
        let arms ← (binding.alts.zip shapes).zipIdx.mapM fun ((alt, (state, row)), index) => do
          let name := s!"$cursorArm{p.line}_{p.col}_{index}"
          let inputTy := Ty.opt state
          let input ← fresh inputTy
          let c := { ctx with locals := { name, slot := input, ty := inputTy, mutable := false } :: ctx.locals }
          let next ← step c alt index (.ident p name)
          unless next.ty == .opt (.tup [state, row]) do
            eerr p "internal: composed cursor arm changed type"
          return { cursor := state, row, input, next := next.e : ForCursorArm }
        let inputTy := Ty.opt (forCursorChoiceType arms)
        let input ← elabE ctx request.prior (some inputTy)
        let slot ← fresh inputTy
        let input ← coerce p input inputTy
        let result ← forCursorChoice p (some slot) arms
        return { result with e := .seq (.assign slot input) result.e }
  let cursorGroups := if cursor.isSome && gs.isEmpty then
    [(.gen p s!"$cursorUnit{p.line}_{p.col}" none (.arrayLit p [.tuple p []]), [])]
    else gs
  if stagePlan.isNone && (!prepared || searchPrepared || cursor.isSome) && !firstDecides && failure.isNone && !cursorGroups.isEmpty &&
      !clauses.any callsManyValued && !pre.any isExcl && cursorGroups.all (fun (g, fs) => plainGen g && !fs.any isExcl) then
    let start := (← get).nslots
    let (preE, unit, c0) ← match pre with
      | [] => pure (none, 0, ctx)
      | _ => do
        let (filt, c1) ← elabFilters ctx pre
        pure (some filt, ← fresh .void, c1)
    let mut c := c0
    let mut levels : Array (Nat × ForDomain × Expr) := #[]
    for (g, fs) in cursorGroups do
      let (slot, domain, c1, bind) ← elabSource c g (cursor.isSome || Choice.hasReturn body)
      let (filt, c2) ← elabFilters c1 fs
      let filt := if fs.isEmpty then bind else match bind with
        | .lit _ => filt
        | e => .seq e filt
      levels := levels.push (slot, domain, filt)
      c := c2
    let newSearch : EM ForSearch := do
      let ls ← levels.toList.mapM fun (slot, domain, filt) => newForLevel slot domain filt
      let head :: tail := ls | eerr p "internal: a for without generators"
      let found ← fresh .logic
      let started ← fresh .logic
      return { head, tail, prelude := preE, found, started, nested := prepared && !searchPrepared }
    if let some request := cursor then
      let search ← newSearch
      let bindings := c.locals.filterMap fun l => if l.slot >= start then some l.slot else none
      let row ← request.outputs.mapM fun name =>
        match c.lookup name with
        | some l => pure l
        | none => eerr p s!"internal: unknown resumable for binding {name}"
      let row : R := ⟨.prim .mkTup (row.map (Expr.local ·.slot)), .tup (row.map (·.ty))⟩
      let saved ← search.capture bindings
      let input ← elabE ctx request.prior (some (.opt saved.ty))
      let slot ← fresh (.opt saved.ty)
      let input ← coerce p input (.opt saved.ty)
      let next ← search.takeFrom bindings (some slot) (some row)
      return { next with e := .seq (.assign slot input) next.e }
    let r ← elabE (bodyCtx c) body bodyExpected
    let r := if r.ty == .never then { r with e := .seq r.e (.lit .void) } else r
    let mutable := c.locals.filterMap fun l => if l.mutable && l.slot >= start then some l.slot else none
    let fx := forClauseEffects fun s => s < start || mutable.contains s
    let n := levels.size
    let undoes := preE.any fx || (levels.toList.zipIdx.any fun ((_, domain, filt), k) =>
      fx domain.code || (k + 1 < n && fx filt))
    if !undoes then
      -- (the nested `forE`s, as `build` makes them)
      let mut inner : R := r
      let mut innermost := true
      for (slot, domain, filt) in levels.toList.reverse do
        let loopE ← iterateForDomain slot domain filt inner.e inner.ty
        if innermost then inner := ⟨loopE, .arr inner.ty⟩
        else match inner.ty with
          | .arr t => inner := ⟨← flattenValues ⟨loopE, .arr inner.ty⟩, .arr t⟩
          | _ => eerr p "internal: nested for"
        innermost := false
      let some filt := preE | return inner
      let .arr t := inner.ty | eerr p "internal: nested for"
      return ⟨← flattenValues ⟨.forE unit (.lit (.arr #[.tup []])) filt inner.e, .arr inner.ty⟩, .arr t⟩
    -- (the search: each step a failure context, `if (step) then body`, in
    -- rounds of `forE`s twice as long as the last, so that the values are
    -- collected in linear time, as for a lazily taken call, `elabLoopGen`)
    let search ← newSearch
    let done ← fresh .logic
    let acc ← fresh (.arr r.ty)
    let v ← fresh (.arr r.ty)
    let size ← fresh .int
    let d ← fresh .int
    let one := Expr.seq (.assign v (.lit Value.emptyArray))
      (.seq (search.take
          (.seq (.assign v (.prim .mkArr [r.e])) (.lit .void))
          (.seq (.assign done (.lit (.logic true))) (.lit .void)))
        (.local v))
    let round := Expr.forE d (p2 .range (.lit (.int 1)) (.local size))
      (p2 .eq (.local done) (.lit (.logic false))) one
    let roundBody := Expr.seq (.assign acc (p2 .concat (.local acc) (← flattenValues ⟨round, .arr (.arr r.ty)⟩)))
      (.ite (isTrueIn done) Expr.brkV
        (.seq (.assign size (p2 .mul (.local size) (.lit (.int 2)))) (.lit .void)))
    -- (a nested continuation's failed outcome breaks the nearest loop, here
    -- this one: forward it, as `elabLoopGen` does)
    let values := match c.forOutcomeSlot with
      | some flag => Expr.ite (.prim .query [.local flag]) (.local acc) (.seq .brk (.prim .userErr []))
      | none => Expr.local acc
    return ⟨.seq search.init (.seq (.assign done (.lit (.logic false)))
      (.seq (.assign acc (.lit Value.emptyArray)) (.seq (.assign size (.lit (.int 16)))
        (.seq (.loop roundBody) values)))), .arr r.ty⟩
  if cursor.isSome then
    eerr p "internal: resumable for header needs flat prepared clauses"
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
        return ⟨← flattenValues ⟨iter, .arr inner.ty⟩, .arr t⟩
      | _ => eerr p "internal: nested for"

end OpenVerse.Front
