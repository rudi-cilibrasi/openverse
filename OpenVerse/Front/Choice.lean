/-
  OpenVerse front end — functions with several values in a program (#235):
  the consumers of recursive groups as functions of their own, returning
  loops, and `inlineMulti`, which inlines every function with several values
  at its calls. The functions themselves are in `ChoiceFns.lean`, and the
  surface side of a choice and its lifting in `ChoiceLift.lean`.
-/
import OpenVerse.Front.ChoiceFns

namespace OpenVerse.Front.Choice

/-- (#283) A consumer in a recursive group's code of a call of a function
    with several values: the failure context that takes the call's values.
    Its `code` is an `if`'s conditions (`conds`), or the clauses of the
    operand of `not`, `option{…}`, `logic{…}`, `first{…}` or the left of
    `or`, its last one binding the operand's value, whose first success is
    taken (`first`); or a `for` bound to a name, which takes them all. `outs`
    are what it gives the code after it: the names the conditions bind, or
    the value's name. -/
structure Consumer where
  pos : Pos
  code : List SExpr
  first : Bool
  conds : Bool
  outs : List String

/-- The clauses `cs` with their last value bound to a name, `v` unless the
    last clause binds one, as `firstOfClauses` does. -/
def valueOf (p : Pos) (v : String) (cs : List SExpr) : List SExpr × String :=
  match cs.getLast? with
  | some (.decl _ x _ _ _) => (cs, x)
  | some e => (cs.dropLast ++ [.decl e.pos v none false e], v)
  | none => ([.decl p v none false (.tuple p [])], v)

/-- (#283) Each outermost consumer in `e` (`Consumer`) of a call that `has`
    sees, replaced by what `f` gives: an `if`'s conditions, or the clauses of
    a block in place of the operand or of the `for`. -/
partial def mapConsumersM [Monad m] (has : SExpr → Bool) (f : Consumer → m (List SExpr)) (e : SExpr) : m SExpr := do
  let go := mapConsumersM has f
  let operand (q : Pos) (x : SExpr) : m SExpr := do
    let (code, v) := valueOf q s!"$nest{q.line}_{q.col}v" (stmtsOf x)
    return .block q (← f { pos := q, code, first := true, conds := false, outs := [v] })
  match e with
  | .ite p cs t u =>
    let cs ← if cs.any has then f { pos := p, code := cs, first := true, conds := true, outs := boundIn cs }
      else cs.mapM go
    return .ite p cs (← go t) (← u.mapM go)
  | .notE p x => if has x then return .notE p (← operand p x) else descendM go e
  | .orE p a b => if has a then return .orE p (← operand p a) (← go b) else descendM go e
  | .optionLit p x => if has x then return .optionLit p (← operand p x) else descendM go e
  | .logicLit p x => if has x then return .logicLit p (← operand p x) else descendM go e
  | .app p (.ident q "$first") [x] false =>
    if has x then return .app p (.ident q "$first") [← operand p x] false else descendM go e
  | .forE p .. =>
    if !has e then descendM go e else
    let v := s!"$nest{p.line}_{p.col}v"
    return .block p (← f { pos := p, code := [.decl p v none false e], first := false, conds := false, outs := [v] })
  | e => descendM go e

/-- (#283) The key of a consumer's name `n` in the types an elaboration
    notes (`$noteTypes`, `Requests.nested`): the consumer's place and `n`. -/
def nestKey (p : Pos) (n : String) : String := s!"{p.file}:{p.line}:{p.col}/{n}"

/-- (#283) The structs and classes `e` constructs with a field whose value has
    something `point` sees. -/
partial def constructsWith (point : SExpr → Bool) (e : SExpr) : List String :=
  (match e with
    | .construct _ n _ fs => if fs.any (anyE point) then [n] else []
    | _ => []) ++ e.children.flatMap (constructsWith point)

/-- (#283) The names a consumer takes from the code of the function `f` it
    is in: those it uses that `f`'s parameters or locals bind, not its own. -/
def Consumer.caps (c : Consumer) (f : MFn) : List String :=
  let own := f.params.map (·.name) ++ localsOf f.body
  let inner := localsOf (.block c.pos c.code)
  (namesUsed (.block c.pos c.code)).filter fun n => own.contains n && !inner.contains n

/-- (#283) A recursive function's (`g`, `f`) consumers of calls of functions
    with several values (`has`), each a function of its own, and its body with
    each a call of it, a plain one: so a consumer in a group's code is a
    consumer like any other, and its own nested one a call of itself. The
    function's body is the consumer as written: its clauses under `first{…}`
    (`<decides>`), or its `for`, then the tuple of what it gives (`outs`),
    the final values of the function's `var`s it sets (copied in as
    `FirstLift`'s are) and `true`. It takes the names it uses from the
    function's code, at the types an earlier elaboration noted (`ty`), and
    the function's type parameters they mention; its effects are the
    function's, `<decides>` for a condition's, and for a `for`'s when that
    elaboration found the `for` can fail (a body that fails fails it). -/
def nestFns (g : String) (f : MFn) (has : SExpr → Bool) (ty : Pos → String → Option STy) :
    Except String (SExpr × List STop) := do
  let isVar (e : SExpr) (n : String) : Bool := anyE (fun | .decl _ x _ true _ => x == n | _ => false) e
  let rw (c : Consumer) : StateT (List STop) (Except String) (List SExpr) := do
    let p := c.pos
    let tyOf (n : String) : StateT (List STop) (Except String) STy := match ty p n with
      | some t => pure t
      | none => throw s!"{p.show}: internal: no type noted for {n} (#283)"
    let caps := c.caps f
    let sets := (setsIn (.block p c.code)).eraseDups.filter fun n => caps.contains n && isVar f.body n
    let capTys ← caps.mapM tyOf
    let outTys ← c.outs.mapM tyOf
    let tps := f.tparams.filter fun tp => capTys.any (styMentions [tp.name])
    if let some tp := f.tparams.find? (fun tp => !tps.contains tp && outTys.any (styMentions [tp.name])) then
      throw s!"{p.show}: {shownFnName g} has several values, and this failure context in its code takes the values of a call and gives a value of type {tp.name}, which none of the names it uses has: not supported yet (#283)"
    let name := s!"{g}$nest{p.line}_{p.col}"
    let params : List SParam := (caps.zip capTys).map fun (n, t) =>
      { name := if sets.contains n then s!"{n}$in" else n, ty := t }
    let setTys := sets.map fun n => ((caps.zip capTys).lookup n).getD (.name "void")
    let copies := (sets.zip setTys).map fun (n, t) => SExpr.decl p n (some t) true (.ident p s!"{n}$in")
    let tup := SExpr.tuple p ((c.outs ++ sets).map (SExpr.ident p ·) ++ [.ident p "true"])
    let body := SExpr.block p (copies ++
      if c.first then [.app p (.ident p "$first") [.block p (c.code ++ [tup])] false] else c.code ++ [tup])
    let decides := c.first || (ty p "$fails").isSome
    let fx := f.fx.filter (· != "decides") ++ (if decides then ["decides"] else [])
    modify (· ++ [.fn p name params tps fx (.tup (outTys ++ setTys ++ [.name "logic"])) body])
    -- (where it was: the call, then what it gives, the `var`s set again)
    let n := s!"$nest{p.line}_{p.col}n"
    let field (i : Nat) : SExpr := .app p (.ident p n) [.int p (i : Int)] false
    let outs := (c.outs.zip outTys).zipIdx.map fun ((o, t), i) =>
      let v := c.code.any (isVar · o)
      SExpr.decl p o (if v then some t else none) v (field i)
    let back := sets.zipIdx.map fun (s, j) => SExpr.set p (.ident p s) none (field (c.outs.length + j))
    let call := SExpr.app p (.ident p name) (caps.map (SExpr.ident p ·)) decides
    return [.decl p n none false call] ++ outs ++ back ++ (if c.conds then [] else c.outs.map (SExpr.ident p ·))
  let (body, fns) ← (mapConsumersM has rw f.body).run []
  return (body, fns)

/-- (#283) The body of a function `f` whose consumers' types are not noted
    yet, for checking only: as `checkBody`, with each consumer noting the
    types of the names it takes and gives (`$noteTypes`, where they are all
    in scope: after an `if`'s conditions, or after the operand's or the
    `for`'s value is bound), and a `for` whether it can fail (`$noteFails`). -/
def noteConsumers (f : MFn) (has : SExpr → Bool) : SExpr :=
  let note (c : Consumer) : Id (List SExpr) :=
    let key := SExpr.str c.pos [.text (nestKey c.pos "")]
    let mark := SExpr.app c.pos (.ident c.pos "$noteTypes") (key :: (c.caps f ++ c.outs).map (SExpr.ident c.pos ·)) false
    let code := if c.first then c.code else c.code.map fun
      | .decl q v t b e => .decl q v t b (.app q (.ident q "$noteFails") [key, e] false)
      | x => x
    if c.conds then code ++ [mark] else code ++ [mark] ++ c.outs.map (SExpr.ident c.pos ·)
  checkBody (Id.run (mapConsumersM has note f.body))

/-- Separate sibling lexical bindings before cells are shared with a helper.
    The original body is retained independently for source admission. -/
private def freshLoopLocal (owner name : String) : StateM Nat String := do
  let serial ← get
  modify (· + 1)
  return s!"$loopLocal{sitePart owner}{serial}'{shownName name}"

private partial def alphaReturnLoopExpr (owner : String) (aliases : List (String × String)) (e : SExpr) :
    StateM Nat (SExpr × List (String × String)) := do
  let fresh := freshLoopLocal owner
  match e with
  | .ident p name => return (.ident p ((aliases.lookup name).getD name), aliases)
  | .decl p name annotation mutable rhs =>
    let (rhs, _) ← alphaReturnLoopExpr owner aliases rhs
    let renamed ← fresh name
    return (.decl p renamed (annotation.map (styRename aliases)) mutable rhs,
      (name, renamed) :: aliases)
  | .gen p name index source =>
    let (source, _) ← alphaReturnLoopExpr owner aliases source
    let renamed ← fresh name
    let updated := (name, renamed) :: aliases
    let (index, updated) ← match index with
      | none => pure (none, updated)
      | some name => do
        let renamed ← fresh name
        pure (some renamed, (name, renamed) :: updated)
    return (.gen p renamed index source, updated)
  | .block p statements =>
    let mut selected := aliases
    let mut output := []
    for statement in statements do
      let (statement, next) ← alphaReturnLoopExpr owner selected statement
      output := output ++ [statement]
      selected := next
    return (.block p output, aliases)
  | .ite p conditions yes no =>
    let mut selected := aliases
    let mut output := []
    for condition in conditions do
      let (condition, next) ← alphaReturnLoopExpr owner selected condition
      output := output ++ [condition]
      selected := next
    let (yes, _) ← alphaReturnLoopExpr owner selected yes
    let no ← no.mapM fun no => do return (← alphaReturnLoopExpr owner aliases no).1
    return (.ite p output yes no, aliases)
  | .forE p clauses body =>
    let mut selected := aliases
    let mut output := []
    for clause in clauses do
      let (clause, next) ← alphaReturnLoopExpr owner selected clause
      output := output ++ [clause]
      selected := next
    let (body, _) ← alphaReturnLoopExpr owner selected body
    return (.forE p output body, aliases)
  | .construct p name arguments fields =>
    let fields ← fields.mapM fun field => do
      match field with
      | .decl q name annotation mutable rhs =>
        return .decl q name (annotation.map (styRename aliases)) mutable (← alphaReturnLoopExpr owner aliases rhs).1
      | field => return (← alphaReturnLoopExpr owner aliases field).1
    return (.construct p ((aliases.lookup name).getD name) (arguments.map (styRename aliases)) fields, aliases)
  -- An alternative of an exclusive choice, which a method's dispatch is made
  -- of (`rwFamCalls`): its guards bind names for its value, as an `if`'s
  -- conditions do for its branch. Renamed apart, the value would use a name
  -- that nothing binds (#764).
  | .app p fn@(.ident _ "$alt") [.block q guards, value] false =>
    let mut selected := aliases
    let mut output := []
    for guard in guards do
      let (guard, next) ← alphaReturnLoopExpr owner selected guard
      output := output ++ [guard]
      selected := next
    let (value, _) ← alphaReturnLoopExpr owner selected value
    return (.app p fn [.block q output, value] false, aliases)
  | .app p fn arguments bracket =>
    let (fn, _) ← alphaReturnLoopExpr owner aliases fn
    let arguments ← arguments.mapM fun argument => do
      match argument with
      | .decl q name annotation mutable rhs =>
        if name.startsWith "?" then
          return .decl q name (annotation.map (styRename aliases)) mutable (← alphaReturnLoopExpr owner aliases rhs).1
        return (← alphaReturnLoopExpr owner aliases argument).1
      | argument => return (← alphaReturnLoopExpr owner aliases argument).1
    return (.app p fn arguments bracket, aliases)
  | e =>
    let changed ← e.mapChildrenM fun child => do return (← alphaReturnLoopExpr owner aliases child).1
    return (changed, aliases)

private def alphaReturnLoopLocals (owner : String) (body : SExpr) : SExpr :=
  ((alphaReturnLoopExpr owner [] body).run 0).1.1

private structure LoopCapture where
  name : String
  pos : Pos
  mutable : Bool := false
  annotation : Option STy := none
  parameter : Option SParam := none

private inductive ReturnLoopSource where
  | range (index : String) (lower upper : SExpr)
  | collection (item : String) (index : Option String) (source : SExpr)
  | cursor (clauses : List SExpr) (outputs : List String) (recursive : List String)
  | loop

/-- The step of a resumable header. An `owned` one keeps its cursor in a
    generated object, so the packet's type does not spell the cursor's. -/
private def forCursorNext (p : Pos) (clauses : List SExpr) (outputs : List String)
    (prior : SExpr) (owned : Bool := false) : SExpr :=
  .app p (.ident p (if owned then "$forOwnedCursorNext" else "$forCursorNext"))
    [.block p clauses, .block p (outputs.map (SExpr.ident p)), prior] false

private def cursorHeaderCells (clauses : List SExpr) : List String :=
  clauses.filterMap fun
    | .decl _ name (some _) true _ => some name
    | _ => none

private def boxCursorHeader (clauses : List SExpr) : List SExpr :=
  clauses.map (cellVars (cursorHeaderCells clauses))

private structure ReturnLoopSite where
  pos : Pos
  key : String
  helper : String
  source : ReturnLoopSource
  body : SExpr
  captures : List LoopCapture
  boxed : List String
  /-- The header calls a function with several values. The body helper's
      choice machine would lift that call out of the header and so change
      the cursor that the header's probe recorded: the header steps in a
      function of its own. -/
  isolated : Bool := false
  /-- A call in the header reaches the loop's own function. That call's
      frame then holds this loop's cursor, and the cursor holds the frame:
      a generated object owns the cursor, and its class names the type. -/
  owned : Bool := false

/-- Where a header's cursor type is noted. A header whose call is found to
    have several values only by a later analysis (an overload's, or a method
    whose name unrelated classes share) is another header then, stepped
    apart: the type noted for the call as written is not its cursor's. -/
private def cursorNoteKey (site : ReturnLoopSite) : String :=
  site.key ++ (if site.isolated then "$isolatedCursor" else "$cursor")

/-- (#780) What the elaboration of a header's cursor (`elabForWith`) says of
    a header it cannot step: a composed choice whose alternatives have rows
    of different types, and clauses that are not a search's after their
    preparation (a call of a function with several values that stays where
    its clause is compiled, inside `first{}` and the like). The types are
    known to the elaboration only. So where a header's cursor is elaborated
    for its type, such a header is noted as refused instead, under its
    loop's position, and the next analysis does not take it: its function
    is refused as one with a header that is none of the forms. That is
    where the header's cursor is noted (`$noteForCursor`), and, for a header
    that calls its loop's own function, which has one value in that
    elaboration, where the cursor's owner is made (`$refinedCursorOwner`).
    Anywhere else they are internal errors. -/
def cursorRowsDiffer : String := "internal: composed cursor alternatives have different row types"
def cursorNotSearch : String := "internal: resumable for header needs flat prepared clauses"
def cursorRefusal (message : String) : Bool :=
  message.endsWith cursorRowsDiffer || message.endsWith cursorNotSearch
def cursorRefusedKey (p : Pos) : String := s!"$cursorRefused:{p.file}:{p.line}:{p.col}"

private def loopSiteKey (owner : String) (p : Pos) : String :=
  s!"$loopReturn:{sitePart owner}:{p.file}:{p.line}:{p.col}/"

private def loopDeclKey (owner : String) (binding : LoopCapture) : String :=
  s!"$loopDeclaration:{sitePart owner}:{binding.pos.file}:{binding.pos.line}:{binding.pos.col}/"

private def loopConcurrent (e : SExpr) : Bool :=
  anyE (fun
    | .app _ (.ident _ name) _ _ =>
      ["$sync", "$race", "$rush", "$branch", "$spawn"].contains name
    | _ => false) e

private partial def loopBodySupported (mv : List String) (e : SExpr)
    (searchHeaders : Bool := false) (bodyChoices : Bool := false) : Bool :=
  let scalar := fun e => loopBodySupported mv e searchHeaders bodyChoices
  match e with
  | .ret _ value => value.all (!loopConcurrent ·)
  -- These scopes select at most one success. Choices in the arms of an
  -- if or in the fallback of or can still reach the producer.
  | .ite _ conditions yes no =>
    !conditions.any loopConcurrent && scalar yes && no.all scalar
  | .optionLit _ value | .logicLit _ value | .notE _ value =>
    !loopConcurrent value
  | .orE _ attempted fallback =>
    !loopConcurrent attempted && scalar fallback
  | .app _ (.ident _ "$first") _ false =>
    !loopConcurrent e
  | .app _ (.ident _ name) _ _ =>
    !["$sync", "$race", "$rush", "$branch", "$spawn"].contains name &&
      (bodyChoices || !(["$choice", "$loop", "$each", "$all"].contains name || mv.contains name)) &&
      e.children.all scalar
  | .forE _ clauses body =>
    if searchHeaders || !hasReturn body then
      !clauses.any hasReturn && !clauses.any loopConcurrent && scalar body
    else match clauses with
      | [.decl _ _ _ false (.range _ lower upper)] =>
        !hasLiftable (markCalls mv lower) && !hasLiftable (markCalls mv upper) &&
          e.children.all scalar
      | [.gen _ _ _ source] =>
        scalar source && !hasLiftable (markCalls mv source) && scalar body
      | _ => false
  | .loop _ body => scalar body
  | e => e.children.all scalar

/-- Recursive return helpers use scalar guards. A condition with its own
    choice search runs in the selector that owns the iteration instead. -/
private partial def iterationGuardChoices (mv : List String) : SExpr → Bool
  | .ret .. => false
  | e@(.ite _ conditions ..) =>
    conditions.any (fun clause => liftsHere (markCalls mv clause)) ||
      e.children.any (iterationGuardChoices mv)
  | e => e.children.any (iterationGuardChoices mv)

private def hasReturningLoop (e : SExpr) : Bool :=
  anyE (fun
    | .forE _ _ body | .loop _ body => hasReturn body
    | _ => false) e

private def loopBinding : SExpr → Option LoopCapture
  | .decl p name annotation mutable _ => some { name, pos := p, mutable, annotation }
  | .gen p name _ _ => some { name, pos := p }
  | _ => none

/-- A break governed by this iteration can reach the producer suffix. -/
private partial def hasOwnLoopBreak : SExpr → Bool
  | .brk .. => true
  | .forE .. | .loop .. => false
  | e => e.children.any hasOwnLoopBreak

/-- Explicit terminal paths cannot reach the helper's next iteration. -/
private partial def loopIterationTerminal : SExpr → Bool
  | .ret .. | .brk .. => true
  | .block _ statements => statements.any loopIterationTerminal
  | .ite _ _ yes (some no) => loopIterationTerminal yes && loopIterationTerminal no
  | .loop _ body => !hasOwnLoopBreak body
  | _ => false

private def uniqueLoopCaptures (bindings : List LoopCapture) : List LoopCapture :=
  bindings.foldl (fun out binding =>
    if out.any (fun prior => prior.name == binding.name && prior.pos == binding.pos) then out else out ++ [binding]) []

private partial def returnLoopSites (owner : String) (f : MFn) (mv : List String)
    (recursiveProducer : String → Bool) : List ReturnLoopSite := Id.run do
  let initial := f.params.map fun param =>
    ({ name := param.name, pos := f.pos, annotation := some param.ty, parameter := some param } : LoopCapture)
  let record (scope : List LoopCapture) (defers : List SExpr) (p : Pos)
      (source : ReturnLoopSource) (body : SExpr) : StateM (List ReturnLoopSite) Unit := do
    let many := anyE (fun
      | .ret _ value => value.any fun operand => hasLiftable (markCalls mv operand)
      | _ => false) body
    let scalar := loopBodySupported mv body
    if hasReturn body && (many || !scalar) &&
        !(scalar && iterationGuardChoices mv body) &&
        loopBodySupported mv body (bodyChoices := true) then
      let inner := localsOf body
      let header := match source with | .cursor clauses _ _ => clauses | _ => []
      let names := namesUsed body ++ header.flatMap namesUsed
      let bindings := match source with
        | .range index .. => [index]
        | .collection item index _ => item :: index.toList
        | .cursor _ outputs _ => outputs
        | .loop => []
      let captures := scope.filter fun binding =>
        !bindings.contains binding.name && !inner.contains binding.name
      let writes := setsIn body ++ header.flatMap setsIn ++ defers.flatMap setsIn
      let boxed := captures.filterMap fun binding =>
        if binding.mutable && names.contains binding.name && writes.contains binding.name then some binding.name else none
      modify (· ++ [{
        pos := p, key := loopSiteKey owner p
        helper := s!"$sourceLoopReturn{sitePart owner}_{p.line}_{p.col}"
        source, body, captures, boxed }])
  let rec walk (scope : List LoopCapture) (defers : List SExpr) (e : SExpr) : StateM (List ReturnLoopSite) Unit := do
    match e with
    | .block _ statements =>
      let mut scope := scope
      let mut defers := defers
      for statement in statements do
        walk scope defers statement
        scope := (loopBinding statement).toList ++ scope
        if isDefer statement then defers := defers ++ [statement]
    | .ite _ conditions yes no =>
      for condition in conditions do walk scope defers condition
      let bound := conditions.filterMap loopBinding
      walk (bound.reverse ++ scope) defers yes
      no.toList.forM (walk scope defers)
    | .forE p [.decl _ index _ false (.range _ lower upper)] body =>
      if !hasLiftable (markCalls mv lower) && !hasLiftable (markCalls mv upper) then
        record scope defers p (.range index lower upper) body
    | .forE p [.gen _ item index source] body =>
      if loopBodySupported mv source && !hasLiftable (markCalls mv source) then
        record scope defers p (.collection item index source) body
    | .forE p clauses body =>
      let alternatives : SExpr → Option (List SExpr) := fun
        | .decl _ _ _ false (.app _ (.ident _ "$choice") values false) => some values
        | _ => none
      let flatChoice := fun clause =>
        (alternatives clause).any fun values => values.all fun value => !liftsHere (markCalls mv value)
      let valid clause := flatChoice clause || !liftsHere (markCalls mv clause)
      let flat := clauses.any flatChoice && clauses.all valid
      let before := clauses.takeWhile (fun clause => (alternatives clause).isNone)
      let scalarPrefix : SExpr → Bool := fun
        | .gen .. | .decl _ _ _ _ (.range ..) => false
        | clause => !liftsHere (markCalls mv clause)
      let composed := before.length < clauses.length && before.all scalarPrefix &&
        (clauses.drop (before.length + 1)).all valid
      let exclusiveClause : SExpr → Bool := fun
        | .decl _ _ _ false value =>
          let marked := markCalls mv value
          liftsAsIf marked || (caseIf "$cursorCase" marked).any (liftsAsIf ·.2)
        | _ => false
      let beforeExclusive := clauses.takeWhile (!exclusiveClause ·)
      let exclusive := beforeExclusive.length < clauses.length && beforeExclusive.all valid &&
        (clauses.drop (beforeExclusive.length + 1)).all valid
      let producer : SExpr → Option String := fun
        | .decl _ _ _ false (.app _ (.ident _ name) args _) =>
          if recursiveProducer name && !args.any (fun arg => liftsHere (markCalls mv arg)) then some name
          else none
        | _ => none
      let recursive :=
        if exclusive then (clauses.flatMap namesUsed).filter recursiveProducer |>.eraseDups
        else if clauses.all (fun clause => (producer clause).isSome || valid clause) then
          (clauses.filterMap producer).eraseDups
        else []
      -- (#761) A clause that calls a function with several values where it
      -- is written (its value, a part of its expression, a filter), not as
      -- a choice's alternative or in a branch; or one with a choice inside
      -- its expression. The call is inlined into the header that the cursor
      -- steps, as an alternative's is, so its values are rows. One such
      -- clause, among clauses with flat choices or none.
      let calling clause := (alternatives clause).isNone && !exclusiveClause clause &&
        liftsHere (markCalls mv clause)
      let beforeCall := clauses.takeWhile (!calling ·)
      -- (a call that stays where its clause is compiled, in a failure
      -- context nested in the clause, is not a clause of the header)
      let calls (e : SExpr) : Bool := (namesUsed e).any mv.contains
      let enclosed : SExpr → Bool := anyE fun
        | .optionLit _ value | .logicLit _ value | .notE _ value => calls value
        | .orE _ attempted _ => calls attempted
        | .ite _ conditions .. => conditions.any calls
        | .app _ (.ident _ name) args false =>
          name.startsWith "$" && !["$dispatch", "$choice"].contains name && args.any fun
            | arg@(.block ..) => calls arg
            | _ => false
        | _ => false
      let called := beforeCall.length < clauses.length && beforeCall.all valid &&
        (clauses.drop (beforeCall.length + 1)).all valid && !clauses.any enclosed
      if (flat || composed || exclusive || called || !recursive.isEmpty) && !clauses.any loopConcurrent &&
          !loopBodySupported mv body then
        record scope defers p (.cursor clauses (boundIn clauses) recursive) body
    | .loop p body => record scope defers p .loop body
    -- A nested loop is not a separately owned return boundary. Keep an
    -- ineligible enclosing loop intact rather than lifting only its child.
    | .app _ (.ident _ "$defer") _ _ => pure ()
    | e => e.children.forM (walk scope defers)
  return ((walk initial [] f.body).run []).2

/-- A return selected by an ordinary search header captures its lexical scope. -/
private structure ChoiceReturnRoute where
  pos : Pos
  key : String
  exit : SExpr
  cleanups : List SExpr
  scope : List LoopCapture
  captures : List LoopCapture

/-- Search-header return lowering carries mutable captures as logical cells. -/
private structure ChoiceReturnLoopSite where
  pos : Pos
  key : String
  iteration : SExpr
  entryScope : List LoopCapture
  entryCaptures : List LoopCapture
  routes : List ChoiceReturnRoute
  boxed : List LoopCapture

private def choiceReturnBindings : SExpr → List LoopCapture
  | .gen p item index _ =>
    { name := item, pos := p } :: index.toList.map fun name => { name, pos := p }
  | e => (loopBinding e).toList

private def choiceReturnRouteKey (owner : String) (p : Pos) : String :=
  s!"$choiceLoopReturn:{sitePart owner}:{p.file}:{p.line}:{p.col}/"

/-- Keep only the innermost binding for a spelling. The production caller
    also alpha-renames source locals before discovery, as for returnLoopSites. -/
private def choiceReturnScope (scope : List LoopCapture) : List LoopCapture :=
  scope.foldl (fun found binding =>
    if found.any (·.name == binding.name) then found else found ++ [binding]) []

private partial def choiceReturnRoutes (owner : String) (scope : List LoopCapture)
    (cleanups : List SExpr) (body : SExpr) : List ChoiceReturnRoute :=
  match body with
  | e@(.ret p _) =>
    let used := namesUsed (.block p (cleanups ++ [e]))
    let scope := choiceReturnScope scope
    [{ pos := p, key := choiceReturnRouteKey owner p, exit := e, cleanups, scope,
       captures := scope.filter fun binding => used.contains binding.name }]
  | .block _ statements => Id.run do
    let mut scope := scope
    let mut cleanups := cleanups
    let mut routes := []
    for statement in statements do
      if isDefer statement then cleanups := cleanups ++ [statement]
      else routes := routes ++ choiceReturnRoutes owner scope cleanups statement
      scope := choiceReturnBindings statement ++ scope
    return routes
  | .ite _ conditions yes no =>
    let bound := conditions.flatMap choiceReturnBindings
    choiceReturnRoutes owner (bound.reverse ++ scope) cleanups yes ++
      no.toList.flatMap (choiceReturnRoutes owner scope cleanups)
  | .forE _ clauses body =>
    choiceReturnRoutes owner ((clauses.flatMap choiceReturnBindings).reverse ++ scope) cleanups body
  | .loop _ body => choiceReturnRoutes owner scope cleanups body
  | .app _ (.ident _ "$returnBoundary") _ false => []
  | e => e.children.flatMap (choiceReturnRoutes owner scope cleanups)

/-- A choice followed by a terminal return can run with that return's
    operand. Delay the statements after the choice, including their defers,
    until the selected iteration's values are taken. -/
private partial def moveTerminalLoopChoices (mv : List String) (e : SExpr)
    (inIteration : Bool := false) : SExpr :=
  let move := fun e => moveTerminalLoopChoices mv e inIteration
  match e with
  | .block p statements =>
    let statements := statements.map move
    let body := SExpr.block p statements
    if !inIteration then body else Id.run do
      let some index := statements.findIdx? (fun statement =>
        !hasReturn statement && liftsHere (markCalls mv statement)) | return body
      let suffix := statements.drop index
      let some (.ret q value) := suffix.getLast? | return body
      let preceding := suffix.dropLast
      if preceding.any (fun statement => hasReturn statement || hasOwnLoopBreak statement) then return body
      let operand := SExpr.block q (preceding ++ [value.getD (.tuple q [])])
      return .block p (statements.take index ++ [.ret q (some operand)])
  | .ite p conditions yes no => .ite p conditions (move yes) (no.map move)
  | .caseE p input arms => .caseE p input (arms.map fun (pat, body) => (pat, move body))
  | .forE p clauses body => .forE p clauses (moveTerminalLoopChoices mv body true)
  | .loop p body => .loop p (moveTerminalLoopChoices mv body true)
  | _ => e

/-- Locate returning loops whose headers require a search. The checking pass
    elaborates the original for before moving the loop into a selector. -/
private partial def choiceReturnLoopSites (owner : String) (f : MFn)
    (mv : List String) : List ChoiceReturnLoopSite := Id.run do
  let initial := f.params.map fun parameter =>
    ({ name := parameter.name, pos := f.pos, annotation := some parameter.ty,
       parameter := some parameter } : LoopCapture)
  let hasSearch := anyE (fun
    | .forE _ clauses body =>
      hasReturn body && clauses.any (fun clause => liftsHere (markCalls mv clause))
    | _ => false)
  let rec walk (scope : List LoopCapture) (e : SExpr) : List ChoiceReturnLoopSite :=
    match e with
    | .block _ statements => Id.run do
      let mut scope := scope
      let mut sites := []
      for statement in statements do
        sites := sites ++ walk scope statement
        scope := choiceReturnBindings statement ++ scope
      return sites
    | .ite _ conditions yes no =>
      walk ((conditions.flatMap choiceReturnBindings).reverse ++ scope) yes ++
        no.toList.flatMap (walk scope)
    | iteration@(.forE p ..) | iteration@(.loop p _) =>
      if (hasSearch iteration || iterationGuardChoices mv iteration) &&
          hasReturn iteration && loopBodySupported mv iteration (searchHeaders := true) then
        let routes := choiceReturnRoutes owner scope [] iteration
        let used := namesUsed iteration
        let entryScope := choiceReturnScope scope
        let entryCaptures := entryScope.filter fun binding => binding.parameter.isSome || used.contains binding.name
        [{ pos := p, key := choiceReturnRouteKey owner p, iteration, entryScope, entryCaptures, routes,
           boxed := (uniqueLoopCaptures (entryCaptures ++ routes.flatMap (·.captures))).filter (·.mutable) }]
      else []
    | .app _ (.ident _ "$defer") _ _ | .app _ (.ident _ "$returnBoundary") _ false => []
    | e => e.children.flatMap (walk scope)
  return walk initial f.body

/-- Notes live immediately before each ORIGINAL return, preserving source
    effect/failure checking and ordinary generator selection. No return or
    cleanup is moved by this checking-only transformation. -/
private partial def noteChoiceReturnLoops (owner : String) (sites : List ChoiceReturnLoopSite)
    (body : SExpr) : SExpr :=
  let routes := sites.flatMap (·.routes)
  let boxed := uniqueLoopCaptures (sites.flatMap (·.boxed))
  let note (p : Pos) (key : String) (captures : List LoopCapture) :=
    SExpr.app p (.ident p "$noteTypes")
      (.str p [.text key] :: [
        .decl p "$observed" (some (.name "int")) false (.tuple p []),
        .app p (.ident p "$captureEvidence") [] false
        ] ++ captures.map (fun capture =>
        .tuple p [.str p [.text capture.name], .ident p capture.name])) false
  let rec go (e : SExpr) : SExpr := Id.run do
    if let .ret p _ := e then
      if let some route := routes.find? (·.pos == p) then
        return .block p [note p route.key route.captures, e]
    match e with
    | .block p statements =>
      return .block p (statements.flatMap fun statement =>
        let changed := go statement
        match statement with
        | .decl q name none true _ =>
          match boxed.find? (fun binding => binding.name == name && binding.pos == q) with
          | some binding => [changed, note q (loopDeclKey owner binding) [binding]]
          | none => [changed]
        | _ => [changed])
    | iteration@(.forE p ..) | iteration@(.loop p _) =>
      let original ← iteration.mapChildrenM (m := Id) fun child => pure (go child)
      match sites.find? (·.pos == p) with
      | some site => return .block p [note p (site.key ++ "$entry/") site.entryCaptures, original]
      | none => return original
    | e => return e.mapChildrenM (m := Id) fun child => pure (go child)
  checkBody (go body)

private def choiceReturnNotesReady (owner : String) (sites : List ChoiceReturnLoopSite)
    (types : List (String × STy)) : Bool :=
  let observed (key : String) (captures : List LoopCapture) :=
    (types.lookup (key ++ "$observed")).isSome &&
      captures.all (fun capture => (types.lookup (key ++ capture.name)).isSome)
  sites.all fun site =>
    observed (site.key ++ "$entry/") site.entryCaptures &&
    site.routes.all (fun route => observed route.key route.captures) &&
    site.boxed.all (fun capture => capture.annotation.isSome ||
      (types.lookup (loopDeclKey owner capture ++ capture.name)).isSome)

private def loopNotesReady (owner : String) (parameters : List TParam) (sites : List ReturnLoopSite) (types : List (String × STy)) : Bool :=
  sites.all fun site => (types.lookup (site.key ++ "$return")).isSome &&
    (match site.source with
     | .collection .. => (types.lookup (site.key ++ site.helper ++ "$iterable")).isSome
     | .cursor .. => (types.lookup (cursorNoteKey site)).isSome
     | _ => true) &&
    parameters.all (fun parameter => (types.lookup (site.key ++ "$type/" ++ parameter.name)).isSome) &&
    site.captures.all fun binding =>
      (types.lookup (site.key ++ binding.name)).isSome &&
      (!site.boxed.contains binding.name || binding.annotation.isSome ||
        (types.lookup (loopDeclKey owner binding ++ binding.name)).isSome)

private partial def noteReturnLoops (owner : String) (ret : STy) (parameters : List TParam) (sites : List ReturnLoopSite) (e : SExpr) : SExpr := Id.run do
  let note (p : Pos) (key : String) (entries : List SExpr) :=
    SExpr.app p (.ident p "$noteTypes") (.str p [.text key] :: entries) false
  let declarations := uniqueLoopCaptures (sites.flatMap fun site => site.captures.filter fun binding =>
    site.boxed.contains binding.name && binding.annotation.isNone)
  let rec go (e : SExpr) : SExpr := Id.run do
    if let some site := sites.find? (·.pos == e.pos) then
      match e with
      | .forE .. | .loop .. =>
        let checked := match site.source, e with
          | .collection _ _ source, .forE q [.gen gp item index _] iteration =>
            let key := site.key ++ site.helper ++ "$iterable"
            let marked := SExpr.app source.pos (.ident source.pos "$noteLoopIterator")
              [.str source.pos [.text key], source] false
            .forE q [.gen gp item index marked] iteration
          | _, _ => e
        let cursor := match site.source with
          | .cursor clauses outputs _ =>
            let p := e.pos
            [.app p (.ident p "$noteForCursor") [.str p [.text (cursorNoteKey site)],
              forCursorNext p (boxCursorHeader clauses) outputs (.ident p "false") site.owned] false]
          | _ => []
        return .block e.pos ([note e.pos site.key
          (.app e.pos (.ident e.pos "$captureEvidence") [] false :: site.captures.map (fun binding => .ident e.pos binding.name) ++
            (.decl e.pos "$return" (some ret) false (.tuple e.pos []) :: parameters.map (fun parameter =>
              .decl e.pos ("$type/" ++ parameter.name) (some (.name parameter.name)) false (.tuple e.pos []))))]
          ++ cursor ++ [checked])
      | _ => pure ()
    match e with
    | .block p statements =>
      let statements := statements.flatMap fun statement =>
        let changed := go statement
        match statement with
        | .decl q name _ true _ =>
          match declarations.find? (fun binding => binding.name == name && binding.pos == q) with
          | some binding => [changed, note q (loopDeclKey owner binding) [.ident q name]]
          | none => [changed]
        | _ => [changed]
      return .block p statements
    | e => return e.mapChildrenM (m := Id) (fun child => pure (go child))
  return checkBody (go e)

/-- Move a direct return out of an initializer before saving its operand.
    Only the normal arm binds the value and runs the original suffix. -/
private partial def loopReturnInitializers (e : SExpr) : SExpr :=
  match e with
  | .block p statements =>
    let rec go : List SExpr → List SExpr
      | [] => []
      | .decl q name ty mutable rhs :: rest =>
        match splitReturnInitializer (fun _ => false) q name ty mutable rhs rest with
        | some moved => moved.map loopReturnInitializers
        | none => .decl q name ty mutable (loopReturnInitializers rhs) :: go rest
      | statement :: rest => loopReturnInitializers statement :: go rest
    .block p (go statements)
  | e => Id.run (e.mapChildrenM fun child => pure (loopReturnInitializers child))

private partial def returnLoopOperands (ret : STy) (tag : String)
    (onBreak : Option SExpr) (packetInsideReturn : Bool) : SExpr → SExpr
  | .ret p value =>
    let saved := s!"{tag}$operand{p.line}_{p.col}"
    let bind := SExpr.decl p saved (some ret) false (value.getD (.tuple p []))
    let packet := SExpr.optionLit p (.ident p saved)
    if packetInsideReturn then .ret p (some (.block p [bind, packet]))
    else .block p [bind, .ret p (some packet)]
  | e@(.brk p) => onBreak.map (fun noneValue => .ret p (some noneValue)) |>.getD e
  | .forE p clauses body => .forE p clauses (returnLoopOperands ret tag none packetInsideReturn body)
  | .loop p body => .loop p (returnLoopOperands ret tag none packetInsideReturn body)
  | e => Id.run (e.mapChildrenM fun child => pure (returnLoopOperands ret tag onBreak packetInsideReturn child))

private partial def boxReturnLoopCaptures (owner : String) (sites : List ReturnLoopSite)
    (types : List (String × STy)) (body : SExpr) : SExpr := Id.run do
  let bindings := uniqueLoopCaptures (sites.flatMap fun site => site.captures.filter fun binding =>
    site.boxed.contains binding.name)
  let rec prepare (e : SExpr) : SExpr := Id.run do
    match e with
    | .block p statements =>
      return .block p (statements.flatMap fun statement =>
        match statement with
        | .decl q name annotation true rhs =>
          match bindings.find? (fun binding => binding.name == name && binding.pos == q) with
          | some binding =>
            let ty := annotation.orElse fun _ => types.lookup (loopDeclKey owner binding ++ name)
            let initial := s!"$loopInitial{sitePart owner}_{q.line}_{q.col}"
            [.decl q initial ty false (prepare rhs), .decl q name ty true (.ident q initial)]
          | none => [prepare statement]
        | _ => [prepare statement])
    | e => return e.mapChildrenM (m := Id) (fun child => pure (prepare child))
  return cellVars (bindings.map (·.name)) (prepare body)

private partial def returnLoopWrittenTypes (e : SExpr) : List STy :=
  let own := match e with
    | .decl _ _ annotation _ _ => annotation.toList
    | .construct _ _ arguments _ => arguments
    | .refineDef _ _ ty _ => [ty]
    | .typeAlias _ _ ty => [ty]
    | .structDef _ _ _ fields => fields.map (·.ty)
    | _ => []
  own ++ e.children.flatMap returnLoopWrittenTypes

def refinedCursorMethod : String := "$takeRefinedRow"

private def refinedCursorEffects : List String := ["reads", "writes", "allocates"]

def refinedCursorViewName (effects : List String) : String :=
  "$refinedRows" ++ String.join (refinedCursorEffects.map fun effect =>
    if effects.contains effect then "1" else "0")

private def refinedCursorView? (p : Pos) (name : String) : Option STop := do
  guard (name.startsWith "$refinedRows")
  let bits := (name.drop "$refinedRows".length).toString.toList
  guard (bits.length == 3 && bits.all (fun c => c == '0' || c == '1'))
  let effects := (refinedCursorEffects.zip bits).filterMap fun (effect, bit) =>
    if bit == '1' then some effect else none
  let effects := if effects.isEmpty then ["computes"] else effects
  let parameter : TParam := { pos := p, name := "$Row", constraint := "type" }
  let row := STy.name parameter.name
  let view := STy.app name [row]
  return .classDef p name [] [parameter] [] [] true []
    [.fn p refinedCursorMethod [] [] ("$abstract" :: effects)
      (.opt (.tup [view, row])) (.tuple p [])]

private def lowerReturnLoops (owner : String) (f : MFn) (sites : List ReturnLoopSite)
    (types : List (String × STy)) : Except String (SExpr × List STop) := do
  let body := boxReturnLoopCaptures owner sites types f.body
  let boxed := (sites.flatMap (·.boxed)).eraseDups
  let mut helpers : List STop := []
  let mut replacements := []
  for site in sites do
    let some ret := types.lookup (site.key ++ "$return") | throw "internal: missing loop return target"
    let substitution ← f.tparams.mapM fun parameter => do
      let some actual := types.lookup (site.key ++ "$type/" ++ parameter.name)
        | throw "internal: missing loop type parameter"
      pure (parameter.name, actual)
    let iterationBody := site.body.mapAll (·.substNames substitution) id
    let collectionSource := match site.source with
      | .collection _ _ source => some source
      | _ => none
    let collectionType ← collectionSource.mapM fun _ => do
      let some ty := types.lookup (site.key ++ site.helper ++ "$iterable")
        | throw "internal: missing loop source type"
      let ty := ty.substNames substitution
      match ty with
      | .arr _ | .map .. => pure ty
      | _ => throw s!"{site.pos.show}: lazy loop return operands require an array, string or map iterator (#686)"
    let isMap := match collectionType with | some (.map ..) => true | _ => false
    let emptyType := match collectionType with
      | some (.arr (.name "$never"))
      | some (.map (.name "$never") _)
      | some (.map _ (.name "$never")) => true
      | _ => false
    if emptyType then
      if let .collection item index source := site.source then
        -- The source can still fail or have effects. Use ordinary iteration
        -- to handle it, with no helper that would bind an impossible item.
        let iteration := SExpr.forE site.pos [.gen site.pos item index (cellVars boxed source)]
          (.tuple site.pos [])
        replacements := replacements ++ [(site.pos, iteration)]
        continue
    let typedCaptures ← site.captures.mapM fun binding => do
      let some ty := types.lookup (site.key ++ binding.name) | throw "internal: missing loop capture"
      let ty := ty.substNames substitution
      let ty := if boxed.contains binding.name then STy.app "$varcell" [ty] else ty
      pure (binding, ty)
    let cursorPacket ← match site.source with
      | .cursor .. =>
        let some ty := types.lookup (cursorNoteKey site) | throw "internal: missing for cursor type"
        pure (some (ty.substNames substitution))
      | _ => pure none
    let used := namesUsed site.body ++ (match site.source with
      | .cursor clauses _ _ => clauses.flatMap namesUsed
      | _ => [])
    let operational := site.captures.filter fun binding =>
      (types.lookup (site.key ++ "$evidence/" ++ binding.name)).isSome
    for binding in operational do
      if binding.mutable then
        throw s!"{site.pos.show}: a loop return capturing a mutable implicit proof is not supported yet (#686)"
    let mut retained := typedCaptures.filter fun (binding, _) =>
      used.contains binding.name || operational.any (fun root => root.name == binding.name)
    let required := [ret] ++ collectionType.toList ++ cursorPacket.toList ++ returnLoopWrittenTypes iterationBody
    let mut needed : List TParam := []
    let mut inferenceOnly : List String := []
    -- Adding an inference input may itself mention another index. Close over
    -- both those input types and transitive bounds before choosing formals.
    for _ in (() :: f.tparams.map (fun _ => ())) do
      needed := f.tparams.filter fun tp =>
        (required ++ retained.map (·.2)).any (styMentions [tp.name])
      for _ in f.tparams do
        let bounds := needed.filterMap (·.upperBound)
        needed := f.tparams.filter fun tp => needed.any (fun prior => prior.name == tp.name) ||
          bounds.any (styMentions [tp.name])
      let mut uncovered := needed.filter fun tp =>
        !(collectionType.toList ++ retained.map (·.2)).any (styMentions [tp.name])
      -- Inputs read solely to infer indices are metadata, and do not taint
      -- independent returned data. Operational proof roots stay real.
      for (binding, ty) in typedCaptures do
        if !retained.any (fun (prior, _) => prior.name == binding.name) &&
            uncovered.any (fun tp => styMentions [tp.name] ty) then
          retained := retained ++ [(binding, ty)]
          inferenceOnly := inferenceOnly ++ [binding.name]
          uncovered := uncovered.filter fun tp => !styMentions [tp.name] ty
    let caps := retained.map fun (binding, ty) =>
      let original := binding.parameter.getD { name := binding.name, ty }
      { original with
        ty, named := false, default := none
        typeValue := original.typeValue || inferenceOnly.contains binding.name
        metadataForward := original.metadataForward || (binding.parameter.isNone &&
          !operational.any (fun root => root.name == binding.name)) }
    let p := site.pos
    let packet := site.helper ++ "$packet"
    let value := site.helper ++ "$returned"
    let noneName := site.helper ++ "$none"
    let noneValue := SExpr.block p
      [.decl p noneName (some (.opt ret)) false (.ident p "false"), .ident p noneName]
    let args := caps.map fun param => SExpr.ident p param.name
    let call (leading : List SExpr) := SExpr.app p (.ident p site.helper) (leading ++ args) false
    let resume (leading : List SExpr) := SExpr.block p
      [.decl p packet (some (.opt ret)) false (call leading),
       .ite p [.decl p value none false (.query p (.ident p packet))]
         (.ret p (some (.ident p value))) (some (.tuple p []))]
    let nested := owner.startsWith "$sourceLoopReturn" || hasReturningLoop iterationBody
    let iterationBody := if nested then loopReturnInitializers iterationBody else iterationBody
    let iterationBody := cellVars boxed iterationBody
    let tparams := needed.map fun tp =>
      { tp with upperBound := tp.upperBound.map (·.substNames substitution) }
    let cursorInput := site.helper ++ "$cursor"
    let advanceName := site.helper ++ "$advance"
    let prepareHeader (clauses : List SExpr) :=
      (boxCursorHeader clauses).map (fun e => cellVars boxed (e.mapAll (·.substNames substitution) id))
    -- The recursive header has its own continuation. A scalar call keeps
    -- its search out of the body helper's choice machine.
    let views := cursorPacket.toList.flatMap STy.names |>.filterMap (refinedCursorView? p)
    let isolate := !views.isEmpty || site.isolated || site.owned || match site.source with
      | .cursor _ _ recursive => !recursive.isEmpty
      | _ => false
    let advance := match site.source, cursorPacket with
      | .cursor clauses outputs _, some ty@(.opt (.tup [prior, _])) =>
        if isolate then
          let body := forCursorNext p (prepareHeader clauses) outputs (.ident p cursorInput) site.owned
          [STop.fn p advanceName ({ name := cursorInput, ty := .opt prior } :: caps) tparams f.fx ty body]
        else []
      | _, _ => []
    let (parameters, helperRet, helperBody, replacement) : List SParam × STy × SExpr × SExpr ← match site.source with
      | .cursor clauses outputs _ => do
        let some (.opt (.tup [prior, .tup rowTypes])) := cursorPacket
          | throw "internal: malformed for cursor type"
        if outputs.length != rowTypes.length then throw "internal: malformed for cursor row"
        let input := cursorInput
        let nextRow := site.helper ++ "$nextRow"
        let row := site.helper ++ "$row"
        let ident := SExpr.ident p
        let project (value : SExpr) (index : Int) := SExpr.app p value [.int p index] false
        let rowValues := project (ident row) 1
        let bindings := (outputs.zip rowTypes).zipIdx.map fun ((name, ty), index) =>
          SExpr.decl p name (some ty) false (project rowValues (Int.ofNat index))
        let bodyWithCells := cellVars (cursorHeaderCells clauses) iterationBody
        let next := call [.optionLit p (project (ident row) 0)]
        let iteration := returnLoopOperands ret site.helper (some noneValue) nested bodyWithCells
        let rest := if loopIterationTerminal iterationBody then [iteration] else [iteration,next]
        let rows := if isolate then SExpr.app p (ident advanceName) (ident input :: args) false
          else forCursorNext p (prepareHeader clauses) outputs (ident input)
        let helperBody := SExpr.block p [.decl p nextRow none false rows,
          .ite p [.decl p row none false (.query p (ident nextRow))]
            (.block p (bindings ++ rest)) (some noneValue)]
        pure ([{ name := input, ty := .opt prior }], .opt ret, helperBody, resume [ident "false"])
      | .range index lower upper =>
        let endName := site.helper ++ "$end"
        let cursor := SExpr.ident p index
        let finish := SExpr.ident p endName
        let next := SExpr.ite p [.cmp p cursor [(">=", finish)]]
          noneValue (some (call [.bin p "+" cursor (.int p 1), finish]))
        let iteration := returnLoopOperands ret site.helper none nested iterationBody
        let iteration := if loopIterationTerminal iterationBody then iteration
          else SExpr.block p [iteration, next]
        let helperBody := SExpr.ite p [.cmp p cursor [(">", finish)]]
          noneValue (some iteration)
        let low := site.helper ++ "$lower"
        let high := site.helper ++ "$upper"
        -- A failed endpoint makes the range empty and reaches the suffix.
        let clauses :=
          [.decl p low (some (.name "int")) false (cellVars boxed lower),
           .decl p high (some (.name "int")) false (cellVars boxed upper)]
        let replacement := if owner.startsWith "$sourceLoopReturn" then
          -- Keep endpoint failure local while normalizing the enclosing
          -- helper's continuation, including for two pure endpoints.
          let bounds := site.helper ++ "$bounds"
          let pair := STy.tup [.name "int", .name "int"]
          let bound (slot : Int) := SExpr.app p (.ident p bounds) [.int p slot] false
          let saved := SExpr.query p (.optionLit p (.block p
            (clauses ++ [.tuple p [.ident p low, .ident p high]])))
          SExpr.ite p [.decl p bounds (some pair) false saved]
            (.block p [.decl p low (some (.name "int")) false (bound 0),
              .decl p high (some (.name "int")) false (bound 1),
              resume [.ident p low, .ident p high]]) (some (.tuple p []))
        else SExpr.ite p clauses (resume [.ident p low, .ident p high]) (some (.tuple p []))
        pure ([{ name := index, ty := .name "int" }, { name := endName, ty := .name "int" }],
          .opt ret, helperBody, replacement)
      | .collection item index source =>
        let ty := collectionType.getD (.arr (.name "$never"))
        let element := match ty with
          | .arr t => t
          | .map key value => .tup [key, value]
          | _ => .name "$never"
        let cursor := if isMap then site.helper ++ "$cursor"
          else index.getD (site.helper ++ "$cursor")
        let items := site.helper ++ "$items"
        let endValue := SExpr.bin p "-" (.member p (.ident p items) "Length") (.int p 1)
        let next := SExpr.ite p [.cmp p (.ident p cursor) [(">=", endValue)]]
          noneValue (some (call [.bin p "+" (.ident p cursor) (.int p 1), .ident p items]))
        let iteration := returnLoopOperands ret site.helper none nested iterationBody
        let iteration := if loopIterationTerminal iterationBody then iteration
          else SExpr.block p [iteration, next]
        let entry := if isMap then site.helper ++ "$entry" else item
        let iteration := if isMap then
          let project (column : Int) := SExpr.app p (.ident p entry) [.int p column] false
          let bindKey := index.toList.map fun name => SExpr.decl p name none false (project 0)
          SExpr.block p (bindKey ++ [.decl p item none false (project 1), iteration])
          else iteration
        let entries := if isMap then
          SExpr.app p (.ident p "$loopMapEntries") [.ident p items] false
          else .ident p items
        let annotation := if isMap then none else some element
        let helperBody := SExpr.ite p [.decl p entry annotation false
          (.app p entries [.ident p cursor] true)] iteration (some noneValue)
        let low := site.helper ++ "$lower"
        let high := site.helper ++ "$upper"
        -- The source and first item share a failure context.
        let replacement := SExpr.ite p
          [.decl p low (some (.name "int")) false (.int p 0),
           .decl p high (some ty) false (cellVars boxed source),
           .cmp p (.member p (.ident p high) "Length") [(">", .int p 0)]]
          (resume [.ident p low, .ident p high]) (some (.tuple p []))
        pure ([{ name := cursor, ty := .name "int" }, { name := items, ty }], .opt ret,
          helperBody, replacement)
      | .loop =>
        -- A break returns an absent result from the helper. Nested loops
        -- own their breaks and remain inside the current iteration.
        let mayBreak := hasOwnLoopBreak iterationBody
        let iteration := if mayBreak then returnLoopOperands ret site.helper (some noneValue) nested iterationBody
          else iterationBody
        let helperBody := if loopIterationTerminal iterationBody then iteration
          else SExpr.block p [iteration, call []]
        let replacement := if mayBreak then resume [] else .ret p (some (call []))
        pure ([], if mayBreak then .opt ret else ret, helperBody, replacement)
    helpers := helpers ++ views ++ advance ++ [.fn p site.helper (parameters ++ caps) tparams f.fx helperRet helperBody]
    replacements := replacements ++ [(p, replacement)]
  let changed := mapE (fun
    | .forE p .. | .loop p _ => replacements.lookup p
    | _ => none) body
  return (changed, helpers)

private def choiceLoopIteration (p : Pos) (clauses : List SExpr) (body : SExpr)
    (stem : String) : SExpr :=
  match clauses with
  | [.decl q index _ false (.range _ low high)] =>
    let integer := some (STy.name "int")
    let lower := stem ++ "$low"
    let upper := stem ++ "$high"
    let cursor := stem ++ "$cursor"
    let ident := SExpr.ident q
    let bounds := [
      SExpr.decl q lower integer false low,
      .decl q upper integer false high,
      .cmp q (ident lower) [("<=", ident upper)]]
    let step := SExpr.block p [
      .decl q index integer false (ident cursor), body,
      .ite p [.cmp p (ident cursor) [(">=", ident upper)]] (.brk p) none,
      .set p (ident cursor) none (.bin p "+" (ident cursor) (.int p 1))]
    .forE p bounds (.block p [.decl q cursor integer true (ident lower), .loop p step])
  | _ => .forE p clauses body

private partial def cursorChoiceLoops (iteration : SExpr) (owner : String) : SExpr :=
  mapE (fun
    | .forE p clauses body =>
      if hasReturn body then
        let stem := s!"{owner}$range{p.line}_{p.col}"
        some (choiceLoopIteration p clauses (cursorChoiceLoops body owner) stem)
      else none
    | _ => none) iteration

private partial def lowerChoiceReturnLoops (owner : String) (f : MFn) (sites : List ChoiceReturnLoopSite)
    (types : List (String × STy)) : Except String (SExpr × List STop) := do
  let boxed := uniqueLoopCaptures (sites.flatMap (·.boxed))
  let boxNames := boxed.map (·.name)
  let storageAnnotation (capture : LoopCapture) (ty : STy) : STy :=
    let declared := capture.annotation.orElse fun _ => types.lookup (loopDeclKey owner capture ++ capture.name)
    if boxNames.contains capture.name then .app "$varcell" [declared.getD ty] else ty
  let rec prepare (e : SExpr) : SExpr := Id.run do
    match e with
    | .decl p name none true rhs =>
      match boxed.find? (fun capture => capture.name == name && capture.pos == p) with
      | some capture => return .decl p name (types.lookup (loopDeclKey owner capture ++ name)) true (prepare rhs)
      | none => return .decl p name none true (prepare rhs)
    | _ => return e.mapChildrenM (m := Id) fun child => pure (prepare child)
  let evidence (key : String) (capture : LoopCapture) : Bool :=
    (types.lookup (key ++ "$evidence/" ++ capture.name)).isSome
  let retain (key : String) (scope used : List LoopCapture) : Except String (List LoopCapture) := do
    let proofs := scope.filter (evidence key)
    for capture in proofs do
      if capture.mutable then
        throw s!"{capture.pos.show}: a loop return capturing a mutable implicit proof is not supported yet (#686)"
    return scope.filter fun capture =>
      evidence key capture || used.any (fun binding => binding.name == capture.name)
  let noted (key : String) (capture : LoopCapture) : Option STy :=
    (types.lookup (key ++ capture.name)).orElse fun _ =>
      types.lookup (key ++ "$evidence/" ++ capture.name)
  let mut helpers := []
  let mut replacements := []
  for site in sites do
    let p := site.pos
    let entryKey := site.key ++ "$entry/"
    let entry ← retain entryKey site.entryScope site.entryCaptures
    let routes ← site.routes.mapM fun route => do
      let captures ← retain route.key route.scope route.captures
      pure { route with captures }
    let name := s!"$chooseLoopReturn{sitePart owner}_{p.line}_{p.col}"
    let selected := name ++ "$selected"
    let packet := name ++ "$packet"
    let slots := name ++ "$slots"
    let ident := SExpr.ident p
    let params ← entry.mapM fun capture => do
      let some ty := noted entryKey capture | throw "internal: missing choice loop selector input"
      let original := capture.parameter.getD { name := capture.name, ty }
      pure { original with
        ty := storageAnnotation capture ty, named := false, default := none
        metadataForward := original.metadataForward || (capture.parameter.isNone && !(evidence entryKey capture)) }
    let routeTypes ← routes.mapM fun route => route.captures.mapM fun capture => do
      let some ty := noted route.key capture
        | throw "internal: missing choice loop return capture"
      pure (if boxNames.contains capture.name then .app "$varcell" [ty] else ty)
    let packetType := STy.opt (.tup (routeTypes.map fun ty => .opt (.tup ty)))
    let selection := mapE (fun
      | .ret q _ => do
        let index ← routes.findIdx? (·.pos == q)
        let values := routes.zipIdx.map fun (route, slot) =>
          if slot == index then SExpr.optionLit q (.tuple q
            (route.captures.map fun capture => .ident q capture.name))
          else .ident q "false"
        some (.block q [.set q (.ident q selected) none (.ident q "true"),
          .ret q (some (.optionLit q (.tuple q values)))])
      | .app q deferFn@(.ident _ "$defer") [cleanup] false =>
        some (.app q deferFn [.ite q [.notE q (.query q (.ident q selected))] cleanup none] false)
      | _ => none) (cellVars boxNames (prepare site.iteration))
    let traversal := cursorChoiceLoops selection name
    let selector := STop.fn p name params f.tparams f.fx packetType (.block p
      [.decl p selected (some (.name "logic")) true (ident "false"), traversal, ident "false"])
    let project (binding : String) (index : Nat) :=
      SExpr.app p (ident binding) [.int p (Int.ofNat index)] false
    let resumes := (routes.zip routeTypes).zipIdx.map fun ((route, types), index) =>
      let input := s!"{name}$input{index}"
      let bound := entry.map (·.name)
      let narrowed := route.captures.filter fun capture =>
        bound.contains capture.name && noted entryKey capture != noted route.key capture
      let aliases := renamedFor input (narrowed.map (·.name))
      let restore := (route.captures.zip types).zipIdx.filterMap fun ((capture, ty), field) =>
        let alias := aliases.lookup capture.name
        if bound.contains capture.name && alias.isNone then none else
          some (SExpr.decl p (alias.getD capture.name) (some ty) false (project input field))
      let code := renameE aliases (cellVars boxNames (.block p (route.cleanups ++ [route.exit])))
      SExpr.ite p [.decl p input none false (.query p (project slots index))]
        (.block p (restore ++ [code])) (some (.tuple p []))
    let saved := SExpr.decl p packet none false (.app p (ident name) (params.map fun param => ident param.name) false)
    let dispatch := SExpr.ite p [.decl p slots none false (.query p (ident packet))]
      (.block p resumes) (some (.tuple p []))
    helpers := helpers ++ [selector]
    replacements := replacements ++ [(p, .block p [saved, dispatch])]
  let lowered := mapE (fun
    | e@(.forE p ..) | e@(.loop p _) =>
      (replacements.lookup p).orElse fun _ => some (cellVars boxNames (prepare e))
    | .decl p name ty mutable rhs => if boxNames.contains name then
        some (cellVars boxNames (prepare (.decl p name ty mutable rhs))) else none
    | .ident p name => if boxNames.contains name then some (.member p (.ident p name) "$VCell") else none
    | _ => none) f.body
  return (lowered, helpers)

/-- (#686) Whether `body` has a returning loop and a use `R.M` whose family
    only the class of `R` tells and no elaboration has noted yet (`sites`,
    `methodFns`). -/
private def unpickedLoopCall (sites : List (Pos × String)) (body : SExpr) : Bool :=
  hasReturningLoop body && (memberUses body).any fun (_, q, _, m) => sites.contains (q, (qualified m).2)

/-- The functions at `kept` with their bodies for checking only
    (`checkBody`), as those kept with one value for an elaboration are. -/
private def checkedAt (kept : List Pos) (tops : List STop) : List STop :=
  tops.map fun
    | .fn p name params tparams fx ret body =>
      .fn p name params tparams fx ret (if kept.contains p then checkBody body else body)
    | top => top

/-- What `inlineMulti` gives: the program with the functions that have
    several values inlined at their calls; whether some are taken lazily
    (#246), whose consumers need a class of stack cells; the uses of methods
    whose family an elaboration is to pick; the calls of overloaded
    functions whose overload an elaboration is to pick; the consumers
    whose names' types an elaboration is to note (#283, `nestFns`); and the
    structs and classes whose field orders it is to note (#283). -/
structure Inlined where
  tops : List STop
  lazy : Bool := false
  /-- Boxed logical locals need their private cell class even if no live
      consumer materializes the helper's body. -/
  logicalCells : Bool := false
  familySites : List (Pos × String) := []
  overloadSites : List (Pos × String) := []
  nestedSites : List String := []
  fieldSites : List String := []
  /-- Top-level overload templates retained through source desugaring for copied suffixes. -/
  copiedOverloadNames : List String := []
  copiedOverloadClashes : List (String × List String) := []
  copiedMethods : CopiedMethods := {}

/-- All producer functions reachable from the root's outgoing calls. -/
private def reachableFunctions (calls : String → List String) (root : String) : List String := Id.run do
  let mut seen : List String := []
  let mut todo := calls root
  while !todo.isEmpty do
    let h := todo.head!
    todo := todo.tail!
    if !seen.contains h then
      seen := seen ++ [h]
      todo := calls h ++ todo
  return seen

/-- The functions of the program that have several values, inlined at their
    calls (see above); the program unchanged when there are none. Also
    whether some are taken lazily (#246), whose consumers need a class of
    stack cells, the uses of methods whose family an elaboration is to pick
    (`methodFns`, by `picks`), and the calls of overloaded functions whose
    overload an elaboration is to pick (by `overloadPicks`). (`inlineFns`
    after `methodFns`: `pending`, the places of functions kept with one value
    until their consumers' types are noted; `checking`, the bodies functions
    are checked with, by place, when they are not theirs; `nestDone`, whether
    their consumers are functions of their own already.) -/
partial def inlineFns (tops : List STop) (eager : List String) (lazy : List String)
    (overloadPicks : List (Pos × String)) (nested : List (String × STy))
    (orders : List (String × List (String × Bool))) (sites methodOvSites : List (Pos × String)) (pending : List Pos := [])
    (checking : List (Pos × SExpr) := []) (nestDone : Bool := false)
    (methodTemplates : List String := []) : Except String Inlined := do
  -- (#283) overloaded functions: each overload a function of its own,
  -- `F$mvK`. A call of `F` is one of the overload the arguments' types
  -- pick, which an earlier elaboration noted by its place (`overloadPicks`),
  -- and as written, with one value, until then (`overloadCandidates`)
  let ovNamesAll := overloadedFns tops
  let ovOf := overloadsOf tops
  -- (which have several values, with every picked call one of its
  -- overload's function; then the functions with the calls of those that
  -- have several values so, the others' calls as written)
  -- (#283) not those kept with one value until their consumers' types are
  -- noted, `pending`)
  let candidates (sel : String → Bool) : List (String × MFn) :=
    (overloadCandidates tops overloadPicks sel).filter (!pending.contains ·.2.pos)
  let mv := multiValued (candidates fun _ => true)
  let fns := candidates mv.contains
  if mv.isEmpty then return { tops, familySites := sites, overloadSites := methodOvSites }
  -- (the overloaded ones with an overload that has several values: their
  -- calls not picked yet are noted by the elaboration, for the next one)
  let ovMv := ovNamesAll.filter fun f => (ovOf f).any (mv.contains ·.1)
  -- (one call takes one overload wherever its code is elaborated; not one
  -- in the clauses after a choice whose alternatives' values are of
  -- different types, copied for each, #335)
  let ovShown (o : String) : String :=
    let f := (o.splitOn "$ov").headD o
    match ((overloadIndex? o).bind fun k => (ovOf f)[k]?) with
    | some (_, _, m) => s!"{shownFnName f}({", ".intercalate (m.params.map (styShow ·.ty))})"
    | none => shownFnName o
  for (q, o) in overloadPicks.filter fun (_, o) => ovNamesAll.contains ((o.splitOn "$ov").headD o) do
    if let some (_, o') := overloadPicks.find? fun (q', o') => q' == q && o' != o then
      throw s!"{q.show}: this call takes the overload {ovShown o} in the clauses copied for one alternative of a choice and {ovShown o'} in those copied for another, and which overload with several values a call takes is decided before types: not supported yet (#283); write the clauses after the choice apart for its alternatives, or give the overloads names of their own"
  let rawMfs := fns.filter (mv.contains ·.1)
  -- (#283) a struct's or class's fields in the order its constructions
  -- evaluate them in, for the lifter where a lazily taken group's code is
  -- normalized: the elaborator's (`TyEnv.fieldOrder`), as an earlier
  -- elaboration noted it (`orders`)
  let fieldOrder (n : String) : FieldOrder := { fields := (orders.lookup n).getD [] }
  let rawCalls (name : String) : List String :=
    (rawMfs.lookup name).map (fun f => (namesUsed f.body).filter mv.contains) |>.getD []
  let recursiveProducer (name : String) : Bool :=
    let group := reachableFunctions rawCalls name
    group.contains name && !group.any eager.contains &&
      group.all fun member => (rawMfs.lookup member).any fun f =>
        let shape (frames : Bool) :=
          loopShape? member mv f.body group frames (f.params.map (·.name)) fieldOrder
        (shape true).isSome || (group.length == 1 && (shape false).isSome)
  -- Source loop exits become a lazy helper only after its lexical input
  -- types and return target have been recorded in their original world.
  let loopTargets := rawMfs.filterMap fun (owner, original) =>
    if !hasReturningLoop original.body then none else
    let f : MFn := { original with body := alphaReturnLoopLocals owner original.body }
    let sites := (returnLoopSites owner f mv recursiveProducer).map fun site =>
      match site.source with
      | .cursor clauses _ _ =>
        let called := (clauses.flatMap namesUsed).filter mv.contains |>.eraseDups
        { site with
          isolated := !called.isEmpty
          owned := called.any fun name =>
            name == owner || (reachableFunctions rawCalls name).contains owner }
      | _ => site
    -- (#780) not a header that the cursor's elaboration has refused
    let sites := sites.filter fun site => (nested.lookup (cursorRefusedKey site.pos)).isNone
    let sites := if sites.any (fun site => match site.source with | .cursor .. => true | _ => false) then
      let selected := choiceReturnLoopSites owner { f with body := moveTerminalLoopChoices mv f.body } mv
      sites.filter fun site => match site.source with
        | .cursor .. => !selected.any (·.pos == site.pos)
        | _ => true
      else sites
    if sites.isEmpty then none else some (owner, f, sites, original.body)
  if !loopTargets.isEmpty then
    -- Even a pure producer can trap in an unused alternative. Keep
    -- recursive header producers lazy in both the probe and the helper.
    let headers := loopTargets.flatMap fun (_, _, loops, _) => loops.flatMap fun site =>
      match site.source with
      | .cursor _ _ recursive => recursive
      | _ => []
    let lazy := (lazy ++ headers).eraseDups
    let needsCells := loopTargets.any fun (_, _, loops, _) => loops.any fun entry =>
      !entry.boxed.isEmpty || match entry.source with
        | .cursor clauses _ _ => !(cursorHeaderCells clauses).isEmpty
        | _ => false
    let ready := loopTargets.all fun (owner, f, sites, _) => loopNotesReady owner f.tparams sites nested
    let mut rewritten := tops
    let mut original := checking
    let mut helperNames := []
    if ready then
      for (owner, f, sites, checked) in loopTargets do
        let (body, helpers) ← lowerReturnLoops owner f sites nested
        rewritten := rewritten.map fun
          | .fn p name params tparams fx ret old =>
            .fn p name params tparams fx ret (if p == f.pos then body else old)
          | top => top
        for helper in helpers do
          if let .classDef _ name .. := helper then
            unless rewritten.any (fun | .classDef _ existing .. => existing == name | _ => false) do
              rewritten := rewritten ++ [helper]
          else rewritten := rewritten ++ [helper]
        original := original ++ [(f.pos, checked)]
        helperNames := helperNames ++ helpers.filterMap fun | .fn _ name .. => some name | _ => none
      let result ← inlineFns rewritten eager (lazy ++ helperNames) overloadPicks nested orders sites methodOvSites pending original nestDone methodTemplates
      return { result with logicalCells := result.logicalCells || needsCells }
    else
      for (owner, f, loops, _) in loopTargets do
        let body := noteReturnLoops owner f.ret f.tparams loops f.body
        rewritten := rewritten.map fun
          | .fn p name params tparams fx ret old =>
            .fn p name params tparams fx ret (if p == f.pos then body else old)
          | top => top
      let result ← inlineFns rewritten eager lazy overloadPicks nested orders sites methodOvSites
        (pending ++ loopTargets.map (·.2.1.pos)) checking nestDone methodTemplates
      return { result with
        logicalCells := result.logicalCells || needsCells
        nestedSites := result.nestedSites ++ loopTargets.flatMap (fun (_, _, loops, _) => loops.map (·.key)) }
  let choiceLoopTargets := rawMfs.filterMap fun (owner, original) =>
    if !hasReturningLoop original.body then none else
    let f : MFn := { original with body := alphaReturnLoopLocals owner original.body }
    let sites := choiceReturnLoopSites owner { f with body := moveTerminalLoopChoices mv f.body } mv
    if sites.isEmpty then none else some (owner, f, sites, original.body)
  if !choiceLoopTargets.isEmpty then
    let ready := choiceLoopTargets.all fun (owner, _, sites, _) => choiceReturnNotesReady owner sites nested
    let mut rewritten := tops
    let mut original := checking
    for (owner, f, loops, checked) in choiceLoopTargets do
      let (body, helpers) ← if ready then lowerChoiceReturnLoops owner f loops nested
        else pure (noteChoiceReturnLoops owner loops f.body, [])
      rewritten := (rewritten.map fun
        | .fn p name params tparams fx ret old =>
          .fn p name params tparams fx ret (if p == f.pos then body else old)
        | top => top) ++ helpers
      if ready && (original.lookup f.pos).isNone then original := original ++ [(f.pos, checked)]
    if ready then
      let result ← inlineFns rewritten eager lazy overloadPicks nested orders sites methodOvSites pending original nestDone methodTemplates
      let needsCells := choiceLoopTargets.any fun (_, _, loops, _) => loops.any (fun entry => !entry.boxed.isEmpty)
      return { result with logicalCells := result.logicalCells || needsCells }
    let result ← inlineFns rewritten eager lazy overloadPicks nested orders sites methodOvSites
      (pending ++ choiceLoopTargets.map (·.2.1.pos)) checking nestDone methodTemplates
    return { result with nestedSites := result.nestedSites ++ choiceLoopTargets.flatMap (fun (_, _, loops, _) => loops.map (·.key)) }
  -- Analyze recursive shapes after source returns have selected their paths.
  -- Keep original bodies for checking and nonrecursive inline boundaries.
  -- (#283) Its own `defer:`s after its value, as an inlined body's are, so
  -- they run as each value leaves it where it is taken lazily or computed
  -- at the call too: with returns, `elimReturns` places them at each exit.
  let exits : List (String × MFn × Option MFn) := rawMfs.map fun (n, f) =>
    if !anyE (fun | .ret .. => true | _ => false) f.body then
      (n, f, some (if (stmtsOf f.body).any isDefer then { f with body := .block f.pos (deferLastLeaves f.pos (stmtsOf f.body)) } else f))
    else
    let retIfs := (stmtsOf f.body).foldl (init := 0) fun acc s => acc + countRetIfs s
    let resultType := if retIfs > 16 || (stmtsOf f.body).any needsReturnBoundary then some f.ret else none
    (n, f, (elimReturns (fun i => s!"$k{i}") 0 (fun _ => false) resultType (stmtsOf f.body) true
      (fun e => hasLiftable (markCalls mv e))).map fun (ss, _) => { f with body := .block f.pos ss })
  -- (#686) A returning loop over a call `R.M` of a method whose name
  -- several unrelated classes declare: until an elaboration has noted the
  -- class of `R` (`sites`, `rootsAt`), the call is as written and its
  -- values are not seen, so the loop is none of the forms above. Its
  -- function is kept with one value for that elaboration, not refused: the
  -- next analysis has the call as its family's, an override's dispatch or
  -- the one implementation's plain call. Only where it would be refused
  -- here: a loop that is one of those forms without the call is noted as
  -- before.
  let unpicked := exits.filterMap fun (_, f, out) =>
    if out.isNone && unpickedLoopCall sites f.body then some f.pos else none
  if !unpicked.isEmpty then
    return ← inlineFns (checkedAt unpicked tops) eager lazy overloadPicks nested orders sites methodOvSites
      (pending ++ unpicked) checking nestDone methodTemplates
  let mfs ← exits.mapM fun
    | (n, _, some g) => pure (n, g)
    | (n, f, none) => throw (if (stmtsOf f.body).any needsReturnBoundary then
          s!"{f.pos.show}: {shownFnName n} has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)"
        else if anyE (fun | x@(.forE ..) | x@(.loop ..) => hasReturn x | _ => false) f.body then
          s!"{f.pos.show}: {shownFnName n} has several values and a return in a for or a loop, which would leave its caller once inlined: not supported yet (#235, #283); find what the loop looks for first (in a var it sets, or a for's array) and return in an if after it"
        else s!"{f.pos.show}: {shownFnName n} has several values and a return inside an expression or a condition, which would leave its caller once inlined (#235, #283): return in an if's branch, a block or a case's arm")
  -- (every name the program binds: parameters, locals, fields, methods)
  let binders : List String := (tops.flatMap fun
    | .fn _ _ ps _ _ _ b => ps.map (·.name) ++ localsOf b
    | .const _ _ _ _ (.structDef _ _ _ fs) => fs.map (·.1)
    | .classDef _ _ _ _ _ _ _ fs ms => fs.map (·.1) ++ ms.flatMap fun
        | .fn _ m ps _ _ _ b => m :: ps.map (·.name) ++ localsOf b
        | _ => []
    | _ => []).eraseDups
  -- (the recursive ones, directly or not, and the ones they call: computed
  -- at the call as the array of their values, `F$all`, #235)
  let callees : List (String × List String) := mfs.map fun (n, f) =>
    let used := namesUsed f.body
    (n, mv.filter used.contains)
  -- (whether `g` reaches itself: each function visited once)
  let reaches (g : String) : Bool := Id.run do
    let mut seen : List String := []
    let mut todo := (callees.lookup g).getD []
    let mut found := false
    while !todo.isEmpty && !found do
      let h := todo.head!
      todo := todo.tail!
      if h == g then found := true
      else if !seen.contains h then
        seen := h :: seen
        todo := ((callees.lookup h).getD []) ++ todo
    return found
  let recs := (mfs.filter fun (n, _) => reaches n).map (·.1)
  -- (#246) the self-recursive ones of the shape of a generator, taken
  -- lazily where they are consumed: computed eagerly, `F$all`, only for the
  -- recursive ones that call them
  -- (#283) or of a strongly connected group of such functions, each's
  -- alternatives calls of the group's: one stack of items for the group,
  -- tagged by function. Parameter instances are inferred from those edges
  -- when the group is elaborated in its consumer's context.
  let reachSet (g : String) := reachableFunctions (fun h => (callees.lookup h).getD []) g
  let groupOf (g : String) : List String :=
    g :: (mfs.map (·.1)).filter fun h => h != g && (reachSet g).contains h && (reachSet h).contains g
  let groupOK (grp : List String) (frames : Bool) : Bool :=
    grp.all fun h => match mfs.lookup h with
      | some f => ((callees.lookup h).getD []).all grp.contains &&
        (loopShape? h mv f.body grp frames (f.params.map (·.name)) fieldOrder).isSome
      | none => false
  -- (#283) one whose calls of its group have code after them (return
  -- frames) is taken lazily too, unless its values can be computed at the
  -- call: when its group is <computes> and keeps no local state, as before,
  -- and nothing it runs prints or calls Err() (`lazy`, after a first
  -- elaboration that found it did)
  let computable (g : String) : Bool := (groupOf g).all fun h => !lazy.contains h &&
    match rawMfs.lookup h with
    | some f => f.fx.contains "computes" && !["reads", "writes", "allocates"].any f.fx.contains &&
        !anyE (fun | .set .. | .decl _ _ _ true _ => true | _ => false) f.body
    | none => false
  -- (#283) the functions one machine takes lazily: a group's strongly
  -- connected functions, and, for one taken lazily (not computable), every
  -- function with several values its code calls, those that one calls, and
  -- so on: a call of one is a choice point of the machine as a call of the
  -- group is, the callee's code a member's
  let machineOf (g : String) : List String :=
    let grp := groupOf g
    if computable g then grp else grp ++ (reachSet g).filter (!grp.contains ·)
  -- (#283) a consumer, in the code of a recursive group taken lazily (one
  -- not computable), of a call of a function with several values, its
  -- group's or another's: a function of its own (`nestFns`), and the
  -- functions analysed again with it. Until an elaboration has noted the
  -- types of the names those take and give, the group's functions are kept
  -- with one value (`pending`), their calls as written, as the uses of a
  -- method's family are in the first elaboration, and their bodies note them
  -- (`noteConsumers`).
  let has (e : SExpr) : Bool := anyE (fun
    | .app _ (.ident _ h) _ _ => mv.contains h || h == "$dispatch"
    | _ => false) e
  -- (the function defined at `p`: a candidate, or an overload of one)
  let isAt (p : Pos) : STop → Bool
    | .fn q n .. => q == p && ((rawMfs.lookup n).isSome || ovNamesAll.contains n)
    | _ => false
  let withBody (p : Pos) (b : SExpr) (t : STop) : STop := match t with
    | .fn q n ps tps fx r _ => if isAt p t then .fn q n ps tps fx r b else t
    | t => t
  -- (#283) the functions `hs` kept with one value until an elaboration has
  -- noted what their normal form needs: their calls as written, their
  -- bodies for checking, noting their consumers' names' types
  -- (`noteConsumers`), as the uses of a method's family are in the first
  -- elaboration; with the others analysed again without them
  let keepPending (hs : List String) : Except String Inlined := do
    let marked := hs.eraseDups.filterMap fun h =>
      (rawMfs.lookup h).map fun f => (f.pos, unpickOverloads ovNamesAll (noteConsumers f has))
    let tops := marked.foldl (fun ts (p, b) => ts.map (withBody p b)) tops
    inlineFns tops eager lazy overloadPicks nested orders sites methodOvSites (pending ++ marked.map (·.1)) checking true methodTemplates
  -- (the functions of the machines of groups taken lazily, not computable)
  let lazyRoots := recs.filter fun g => !computable g && !(groupOf g).any eager.contains
  if !nestDone then
    let consumers (f : MFn) : List Consumer :=
      ((mapConsumersM (m := StateM (List Consumer)) has (fun c => do modify (· ++ [c]); pure c.code) f.body).run []).2
    let members := (lazyRoots.flatMap machineOf).eraseDups
    let targets := members.filterMap fun g =>
      (rawMfs.lookup g).bind fun f => if (consumers f).isEmpty then none else some (g, f)
    if !targets.isEmpty then
      let ty (p : Pos) (n : String) : Option STy := nested.lookup (nestKey p n)
      if targets.all fun (_, f) => (consumers f).all fun c => (c.caps f ++ c.outs).all (ty c.pos · |>.isSome) then
        let mut tops := tops
        let mut checking := checking
        for (g, f) in targets do
          let (body, more) ← nestFns g f has ty
          -- (each still checked as written)
          checking := checking ++ tops.filterMap fun t => match t with
            | .fn q _ _ _ _ _ b => if isAt f.pos t then some (q, b) else none
            | _ => none
          tops := tops.map (withBody f.pos body) ++ more
        return ← inlineFns tops eager lazy overloadPicks nested orders sites methodOvSites pending checking true methodTemplates
      let r ← keepPending (targets.flatMap fun (g, _) => groupOf g)
      return { r with nestedSites := targets.flatMap fun (_, f) => (consumers f).map (nestKey ·.pos "") }
  let loops : List String := recs.filter fun g =>
    let grp := groupOf g
    -- An incomplete tail erases its values. A returning any-valued group
    -- may also yield non-void values, so forwarding its recursive values
    -- unchanged would lose that erasure. Keep ordinary eager lowering.
    let returning := grp.any fun h => ((rawMfs.lookup h).map fun f =>
      anyE (fun | .ret .. => true | _ => false) f.body).getD false
    let erasesRecursive := returning && grp.any fun h => ((mfs.lookup h).map fun f =>
      styEq f.ret (.name "any") && anyE (fun
        | i@(.ite ..) => !isBranchy.complete i && (namesUsed i).any grp.contains
        | _ => false) f.body).getD false
    if grp.any eager.contains || erasesRecursive then false else
    let shaped (frames : Bool) : Bool :=
      let grp := if frames then machineOf g else groupOf g
      match mfs.lookup g with
      | some f => if grp.length == 1 then (callees.lookup g).getD [] == [g] &&
          (loopShape? g mv f.body (frames := frames) (params := f.params.map (·.name)) (fieldOrder := fieldOrder)).isSome
        else groupOK grp frames
      | none => false
    shaped false || (!computable g && shaped true)
  let loopGroups : List (String × List String) :=
    loops.filterMap fun g => let grp := machineOf g; if grp.length > 1 then some (g, grp) else none
  let inMachine (n : String) : Bool := loopGroups.any (·.2.contains n)
  -- (#283) a struct or class constructed with a choice point in a field, in
  -- the code of a group taken lazily, is lifted in its fields' order, the
  -- elaborator's: until an elaboration has noted it, the group is kept with
  -- one value and the elaboration notes it (`Requests.fieldOrders`), as it
  -- notes consumers' types
  let unordered (g : String) : List String :=
    let grp := machineOf g
    let point (x : SExpr) : Bool := isChoice x || match x with
      | .app _ (.ident _ h) _ _ => grp.contains h
      | _ => false
    (grp.flatMap fun h => ((mfs.lookup h).map fun f => constructsWith point f.body).getD []).filter
      (orders.lookup · |>.isNone)
  let waiting := lazyRoots.filter fun g => !loops.contains g && !(unordered g).isEmpty
  if !waiting.isEmpty then
    let r ← keepPending (waiting.flatMap machineOf)
    return { r with fieldSites := (waiting.flatMap unordered).eraseDups }
  let mut needAll := recs.filter (!loops.contains ·)
  let mut grew := true
  while grew do
    grew := false
    for g in needAll do
      for h in (callees.lookup g).getD [] do
        if !needAll.contains h then needAll := needAll ++ [h]; grew := true
  -- (effect-free: <computes> and no local state; that nothing they may
  -- run prints or calls `Err()` is checked on their Verse Core code, which
  -- shows every call, `checkEager`)
  for g in needAll do
    let some f := rawMfs.lookup g | continue
    -- A loop's return helper (#686) steps itself, and a dispatch in its code
    -- is no call that its machine takes lazily: said of the loop, which is
    -- what the program wrote (#764), not of a function the compiler made.
    let dispatching := g.startsWith "$sourceLoopReturn" && anyE (fun
      | .app _ (.ident _ "$dispatch") _ false => true
      | _ => false) f.body
    let why (w : String) : String :=
      if dispatching then
        s!"{f.pos.show}: this loop is left by a return of a function with several values, and its body or a returned value calls an overridden method with several values: not supported yet (#686, #764); call the method among a for's clauses or an if's conditions"
      else
        s!"{f.pos.show}: {shownFnName g} has several values and is recursive, or called by a recursive one, {w}: {eagerWhy}"
    if !f.fx.contains "computes" || ["reads", "writes", "allocates"].any f.fx.contains then throw (why "and it is not <computes>")
    if anyE (fun | .set .. | .decl _ _ _ true _ => true | _ => false) f.body then
      throw (why "and it has a var or a set")
  for (n, f) in rawMfs do
    if (fns.filter (·.1 == n)).length > 1 then
      throw s!"{f.pos.show}: {shownFnName n} has several values and is overloaded: such functions are not supported yet (#235)"
    -- (its body is inlined where other names may be in scope: so neither
    -- its name nor a name its body uses from outside may be bound anywhere)
    if binders.contains n then
      throw s!"{f.pos.show}: {n} has several values, and {n} is also the name of a parameter, local, field or method: rename one, as calls of {n} are inlined (#235)"
    -- (a name its body uses from outside that is bound somewhere too is
    -- checked where the body is inlined, `$freeNames`, #283)
  -- (the functions machines take that are not recursive, inlined elsewhere
  -- with their bodies as written: in a machine, with their returns taken out
  -- as a group's are, #283)
  let memberFns := mfs.filter fun (n, _) => !loops.contains n && inMachine n
  let mfs := mfs.map fun (n, f) =>
    (n, if loops.contains n then f else if needAll.contains n then
      { f with body := eraseReturnTails f.body } else (rawMfs.lookup n).getD f)
  -- (no use as a value)
  let defaults (ps : List SParam) : List SExpr := ps.filterMap (·.default)
  let bodies : List SExpr := tops.flatMap fun
    | .fn _ _ ps _ _ _ b => b :: defaults ps
    | .const _ _ _ _ e => [e]
    | .classDef _ _ _ _ _ _ _ fs ms => fs.filterMap (·.default) ++ ms.flatMap fun
        | .fn _ _ ps _ _ _ b => b :: defaults ps
        | _ => []
  for b in bodies do
    if let some (p, n) := valueUse? mv b then
      throw s!"{p.show}: {n} has several values, so it cannot be used as a function value (#235)"
  -- (each call inlined; each function kept for checking only)
  -- (for each, the names its body uses from outside that are bound
  -- somewhere too: where it is inlined, they must not be in scope)
  let clash : List (String × List String) := mfs.filterMap fun (n, f) =>
    let own := f.params.map (·.name) ++ localsOf f.body
    let us := (namesUsed f.body).eraseDups.filter fun u => u != n && !own.contains u && binders.contains u
    if us.isEmpty || (recs.contains n && !loops.contains n) then none else some (n, us)
  let picked : SExpr → SExpr := if overloadPicks.isEmpty then id else pickOverloads ovNamesAll overloadPicks mv.contains
  let go (e : SExpr) : StateT Nat (Except String) SExpr :=
    inlineCalls mfs (picked e) recs loops clash (groups := loopGroups) (fieldOrder := fieldOrder) (memberFns := memberFns)
  -- Pending functions retain the original loop for source checking. The
  -- separate cursor probe needs the same producer lowering as the helper.
  let rec cursorNotes (e : SExpr) : StateT Nat (Except String) SExpr := do
    match e with
    | .app p f@(.ident _ "$noteForCursor") [key, probe] false =>
      return .app p f [key, ← go probe] false
    | _ => descendM cursorNotes e
  let goPs (ps : List SParam) : StateT Nat (Except String) (List SParam) :=
    ps.mapM fun sp => do return { sp with default := ← sp.default.mapM go }
  let (tops', nextSite) ← (tops.filterMapM (m := StateT Nat (Except String)) fun t => do
    match t with
    | .fn p n ps tps fx r b =>
      -- (#283) one kept with one value until its consumers' types are
      -- noted: its body for checking already, as written
      if pending.contains p then return some (.fn p n ps tps fx r (← cursorNotes b))
      -- (checked as written, when its consumers are functions of their own)
      let checked := (checking.lookup p).getD b
      -- (an overload of an overloaded one, #283: as its own analysis says,
      -- by its place: one with several values kept for checking, one
      -- with one value compiled, as it is called as written)
      if ovMv.contains n then
        let own := ((ovOf n).find? fun (_, q, _) => q.line == p.line && q.col == p.col && q.file == p.file).map (·.1)
        if own.any mv.contains then return some (.fn p n ps tps fx r (checkBody checked))
        return some (.fn p n (← goPs ps) tps fx r (← go b))
      -- (its own name kept, so that messages name it: nothing calls it)
      if mv.contains n then
        return some (.fn p n ps tps fx r (checkBody checked))
      return some (.fn p n (← goPs ps) tps fx r (← go b))
    | .const p n sp ty e => return some (.const p n sp ty (← go e))
    | .classDef p n nsp tps sp pa ii fs ms =>
      let fs' ← fs.mapM fun f => do return { f with default := ← f.default.mapM go }

      let ms' ← ms.mapM fun
        | .fn p2 n2 ps2 tps2 fx2 r2 b2 => do return STop.fn p2 n2 (← goPs ps2) tps2 fx2 r2 (← go b2)
        | m => pure m
      return some (.classDef p n nsp tps sp pa ii fs' ms')).run 0
  -- (`F$all` for each that needs one: the array of its values)
  let (alls, _) ← (needAll.filterMapM (m := StateT Nat (Except String)) fun g => do
    let some f := mfs.lookup g | return none
    let f := { f with body := eraseReturnTails f.body }
    let namedCalls := (namesUsed f.body).any fun h =>
      ((mfs.lookup h).map fun callee => callee.params.any (·.named)).getD false
    let body ← if namedCalls then inlineCalls mfs f.body needAll [] clash (groups := loopGroups) (fieldOrder := fieldOrder)
      else pure f.body
    -- The collector transports the original arguments into its checked
    -- body. Actual execution still checks their propagated provenance.
    let ps := f.params.map fun sp =>
      { sp with named := false, default := none, metadataForward := true }
    return some (.fn f.pos s!"{g}$all" ps f.tparams (f.fx.filter (· != "decides"))
      (.arr f.ret) (allBody (if namedCalls then [] else needAll) f.ret body))).run nextSite
  -- (#283) each overload of an overloaded one kept as `F$mvK` too, for
  -- its signature where its calls are inlined (effects, defaults)
  let reachesRecursive (g : String) : Bool := Id.run do
    let mut todo := [g]
    let mut seen : List String := []
    while !todo.isEmpty do
      let h := todo.head!
      todo := todo.tail!
      if recs.contains h then return true
      if !seen.contains h then
        seen := h :: seen
        todo := (callees.lookup h).getD [] ++ todo
    return false
  let copiedOverloadNames := (ovMv.flatMap fun f =>
    (ovOf f).filterMap fun (k, _, _) => if mv.contains k then some k else none) ++ methodTemplates
  let ovKept : List STop := ovMv.flatMap fun f => (ovOf f).filterMap fun (k, p, m) =>
    if mv.contains k then some (.fn p k m.params m.tparams m.fx m.ret (checkBody ((checking.lookup p).getD m.body))) else none
  -- Carry templates through the source transforms in private declarations,
  -- extracted before signature/elaboration. Checking stubs stay unchanged.
  let (copyTemplates, _) ← ((ovMv.flatMap ovOf ++ methodTemplates.filterMap fun name =>
      (rawMfs.lookup name).map fun body => (name, body.pos, body)) |>.filterMapM (m := StateT Nat (Except String)) fun (k, p, m) => do
    if !copiedOverloadNames.contains k then return none
    let params ← goPs m.params
    let body ← if reachesRecursive k then do
        -- Normalize the selected entry with the ordinary recursion metadata,
        -- not its raw body with the late copied inliner's empty recs/loops.
        -- All supplied formals leave omitted defaults to the outer call's
        -- normal binder, while preserving lazy $loop / eager $all carriers.
        let arguments := m.params.map fun sp =>
          let value := SExpr.ident p sp.name
          if sp.named then SExpr.decl p ("?" ++ sp.name) none false value else value
        go (.app p (.ident p k) arguments (m.fx.contains "decides"))
      else go (((mfs.lookup k).getD m).body)
    return some (STop.fn p ("$copiedOverload:" ++ k) params m.tparams m.fx m.ret body)).run nextSite
  -- (#283) the calls of those with an overload that has several values whose
  -- overload is not picked yet: the elaboration notes it, for the next one
  -- (`Requests.overloads`)
  let ovSites := (bodies.flatMap callUses).filter fun (q, f) => ovMv.contains f && (overloadPicks.lookup q).isNone
  return { tops := tops' ++ copyTemplates ++ ovKept ++ alls, lazy := !loops.isEmpty, familySites := sites,
           overloadSites := (ovSites ++ methodOvSites).eraseDups, copiedOverloadNames,
           copiedOverloadClashes := clash.filter fun (n, _) => copiedOverloadNames.contains n }

/-- (#283) The calls of `h` in `e` that `here` sees made calls of `h'`. -/
partial def renameCalls (h h' : String) (here : SExpr → Bool) : SExpr → SExpr :=
  mapE fun
    | e@(.app p (.ident r n) as br) =>
      if n == h && here e then some (.app p (.ident r h') (as.map (renameCalls h h' here)) br) else none
    | _ => none

/-- (#283) The callee of the call at `q` in `e`. -/
partial def calleeAt (q : Pos) (e : SExpr) : Option String :=
  match e with
  | .app p (.ident _ h) _ _ => if p == q then some h else e.children.findSome? (calleeAt q)
  | _ => e.children.findSome? (calleeAt q)

/-- (#283) Each call of `calls`, by its place and the function whose code it
    is in, a call of a copy of its callee of its own, `F$copyK` (`K` the
    call's place in `calls`, shown as `F`; its calls of itself the copy's):
    so the machine of a lazily taken group that takes the callee at another
    instance of its type parameters than the one it took first takes that
    copy as another member, at that instance (`Requests.instanceCalls`), as
    a function called at two instances is two members. Refused for a callee
    recursive with that function, or with another: a group's own function
    is taken at one instance for a whole search. -/
def instanceCopies (tops : List STop) (calls : List (Pos × String)) : Except String (List STop) :=
  calls.zipIdx.foldlM (init := tops) fun tops ((q, caller), k) => do
    let fnNamed (n : String) : List STop := tops.filter fun | .fn _ m .. => m == n | _ => false
    let codeOf : STop → List SExpr
      | .fn _ _ ps _ _ _ b => b :: ps.filterMap (·.default)
      | _ => []
    let some h := (fnNamed caller).findSome? fun t => (codeOf t).findSome? (calleeAt q)
      | throw s!"{q.show}: internal: no call here in {shownFnName caller} (#283)"
    let [.fn p _ ps tps fx r b] := fnNamed h
      | throw s!"{q.show}: {shownFnName h} has several values and is overloaded, and this call is taken at another instance of its type parameters than another in one search: not supported yet (#283)"
    -- (whether `a` calls `z`, directly or not)
    let calls (n : String) : List String := (fnNamed n).flatMap fun t => (codeOf t).flatMap namesUsed
    let reaches (a z : String) : Bool := Id.run do
      let mut seen : List String := []
      let mut todo := calls a
      while !todo.isEmpty do
        let x := todo.head!
        todo := todo.tail!
        if x == z then return true
        if !seen.contains x then
          seen := x :: seen
          todo := calls x ++ todo
      return false
    if reaches h caller || (calls h).any (fun x => x != h && reaches x h) then
      throw s!"{q.show}: {shownFnName h} has several values and is called here at another instance of its type parameters than its machine takes it at in one search, and it is recursive with {if reaches h caller then shownFnName caller else "another function"}: not supported yet (#283)"
    let copy := s!"{h}$copy{k}"
    let rename (here : SExpr → Bool) : SExpr → SExpr := renameCalls h copy here
    let inFn (t : STop) (f : SExpr → SExpr) : STop := match t with
      | .fn p' n ps' tps' fx' r' b' => .fn p' n (ps'.map fun sp => { sp with default := sp.default.map f }) tps' fx' r' (f b')
      | t => t
    let tops := tops.map fun t => match t with
      | .fn _ n .. => if n == caller then inFn t (rename (·.pos == q)) else t
      | t => t
    return tops ++ [inFn (.fn p copy ps tps fx r b) (rename fun _ => true)]

/-- `inlineFns` after `methodFns`: methods with several values as functions
    first (#283; `reserved`: the members of built-in types and of the
    prelude). `nested`: the types of the names consumers take and give, as an
    earlier elaboration noted them (#283); `instanceCalls`, the calls to give
    copies of their callees of their own (`instanceCopies`). -/
def inlineMulti (tops : List STop) (reserved : List String := []) (eager : List String := [])
    (picks : List (Pos × String) := []) (lazy : List String := []) (overloadPicks : List (Pos × String) := [])
    (nested : List (String × STy) := []) (orders : List (String × List (String × Bool)) := [])
    (instanceCalls : List (Pos × String) := []) : Except String Inlined := do
  let (tops, sites, methodOvSites, copiedMethods) ← methodFns tops reserved picks overloadPicks
  let tops ← instanceCopies tops instanceCalls
  let methodTemplates := (copiedMethods.families.flatMap fun (slot, family) =>
    family.impls.map fun owner => methodFnName owner slot).eraseDups
  let result ← inlineFns tops eager lazy overloadPicks nested orders sites methodOvSites
    (methodTemplates := methodTemplates)
  return { result with copiedMethods }

end OpenVerse.Front.Choice
