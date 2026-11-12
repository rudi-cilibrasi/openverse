/-
  OpenVerse front end — casts that refine type arguments (#243), their
  surface side.

  In generic code, a cast `D := T[X]` whose class `T` fixes or repeats the
  type arguments of `X`'s class (`dup(t) := class(pair(t, t))`, with
  `X:pair(a, b)`) holds only under a refinement of the code's type
  parameters (`a = b`), which Verse Core gives a dispatch to classes with
  pins (`Typed.dispatch`), not a cast. So the branch it guards is lifted
  into a generic function, `$refine…(D, captured locals…)`, typed in the
  refined world, and the `if` becomes a dispatch to it:

      if (D := dup[P]) then Body else Else
        ⟶  if (P's class is dup) then $refine(P, X…) else Else

  A cast that is a clause of any other failure context takes the rest of it
  as its branch so: `pre; D := dup[P]; rest` is `pre; if (D := dup[P]) then
  {rest} else fail` (`castClause?`, `noValue`, `castRestClauses`).

  The elaborator finds such a cast in a first elaboration and asks for the
  function (`Lift`); the program is then elaborated again with it, made
  here from the branch, with the refinement applied to the types written in
  it.
-/
import OpenVerse.Front.Choice

namespace OpenVerse.Front.Refine

/-- How a lifted branch returns an explicit exit and copies its locals.
    The return operand is bound before cleanup, and the tuple is read after. -/
structure Exits where
  ret : Option (Option (String × STy) × List SExpr) := none
  brk : Option (List SExpr) := none
  deriving Inhabited

/-- The source storage of a mutable capture, before Core frame tags and
    final slot numbers exist. -/
structure Storage where
  frame : String
  name : String
  args : List STy
  deriving Inhabited

/-- A refining cast's branch, lifted into a generic function (#243). -/
structure Lift where
  /-- The `if`'s position and the name its condition binds: the key. -/
  pos : Pos
  bound : String
  /-- The class cast to: it and the classes below it get pins in Verse
      Core, which the dispatch to the function refines by. -/
  target : String
  /-- The function made from the branch: its name, its parameters (the
      bound name first, then the locals the branch uses, each at its type
      under the refinement), type parameters, effects and result type. -/
  name : String
  params : List SParam
  tparams : List TParam
  specs : List String
  ret : STy
  /-- The refinement, on the enclosing function's type parameters, for the
      types written in the branch. -/
  subst : List (String × STy)
  /-- The branch's own type, which `ret` is under the refinement, when the
      dispatch takes it: its `else` gives no value and nothing around it gave
      one (a cast with the rest of a failure context as its branch). -/
  branchTy : Option STy := none
  /-- The type arguments the cast opens (#250), which `target` has and the
      object's type does not name: each type parameter of the function made
      for them, with the name of `target`'s type parameter it stands for,
      whose value it reads from the object's hidden field. -/
  opened : List (String × String) := []
  /-- The branch, when it is not taken from the source as written: in a
      method, with the members of `Self` it names bare made `Self.member`. -/
  body : Option SExpr := none
  /-- In a class's copy of an interface's default (#53): `$in` and the
      class, as the copies and the interface's own default share the
      source's places (`Ctx.liftTag`); such a lift always has its `body`. -/
  tag : String := ""
  /-- Refinements moved into an immediate continuation use its local
      copies, rather than the source frame's capture metadata. -/
  continuationScope : String := ""
  exits : Exits := {}
  /-- Whether executing the lifted then-block can wait. The generated
      function may need `<suspends>` for the dispatch even when it never waits. -/
  waits : Bool := false
  /-- Source suspension capability, distinct from frame-only lowering. -/
  sourceSuspends : Bool := false
  storage : List (String × Storage) := []
  /-- Source repetition context, preserved when the lift becomes a function. -/
  inRepeat : Bool := false
  /-- Lexical restrictions and active default dependencies of the source. -/
  sourceContext : Choice.SourceContext := {}
  /-- The original copy tag, separate from context-sensitive request identity. -/
  liftTag : Option String := none
  inlineScopes : List String := []
  deriving Inhabited

def keyOf (p : Pos) (bound : String) (tag : String := "") : String := s!"{p.file}:{p.line}:{p.col}:{bound}{tag}"

def Lift.key (l : Lift) : String := keyOf l.pos l.bound l.tag

/-- Whether `pr` holds of `e` or a part of it outside the `loop`s in it. -/
partial def anyOutsideLoops (pr : SExpr → Bool) (e : SExpr) : Bool :=
  pr e || match e with
    | .loop .. => false
    | e => e.children.any (anyOutsideLoops pr)

/-- The first part of `e` (outside its `loop`s, if `outside`) for which
    `pr` holds. -/
partial def findPart (pr : SExpr → Bool) (outside : Bool) (e : SExpr) : Option SExpr :=
  if pr e then some e
  else match e with
    | .app _ (.ident _ "$forPrepare") _ false => none
    | .loop .. => if outside then none else e.children.findSome? (findPart pr outside)
    | e => e.children.findSome? (findPart pr outside)

/-- The type names written in `e` (in declarations and constructions). -/
partial def typeNames (e : SExpr) : List String :=
  if let .app _ (.ident _ "$constructHints") _ false := e then [] else
  let own : List String := match e with
    | .decl _ _ (some t) _ _ => t.allNames
    | .construct _ _ ts _ => ts.flatMap STy.allNames
    | _ => []
  own ++ e.children.flatMap typeNames

/-- `e` with the type names in `σ` substituted in the types written in it
    (declarations, constructions). -/
partial def substTypes (σ : List (String × STy)) : SExpr → SExpr :=
  Choice.mapE fun
    | .decl p n (some t) v x => some (.decl p n (some (t.substNames σ)) v (substTypes σ x))
    | .construct p n ts fs => some (.construct p n (ts.map (·.substNames σ)) (fs.map (substTypes σ)))
    | _ => none

def Exits.substTypes (exits : Exits) (σ : List (String × STy)) : Exits :=
  { ret := exits.ret.map fun (binding, pack) =>
      (binding.map fun (n, t) => (n, t.substNames σ), pack.map (Refine.substTypes σ))
    brk := exits.brk.map (·.map (Refine.substTypes σ)) }

def liftedBreak (p : Pos) : SExpr := .app p (.ident p "$refineBreak") [] false

def isBreak : SExpr → Bool
  | .brk _ | .app _ (.ident _ "$refineBreak") [] false => true
  | _ => false

/-- `e` with its `return`s, and its `break`s that leave it, made `Err()`:
    for the type of what it gives when it ends. -/
def exitsAsErr (e : SExpr) : SExpr :=
  let err (q : Pos) : SExpr := .app q (.ident q "Err") [] false
  let e := Choice.mapE (fun | .ret q _ => some (err q) | _ => none) e
  Choice.mapE (fun
    | .brk q => some (err q)
    | b@(.app _ (.ident _ "$refineBreak") [] false) => some (err b.pos)
    | l@(.loop ..) => some l
    | _ => none) e

/-- An expression that fails, giving no value, of every type: the `else` of
    a cast that takes the rest of its failure context as its branch. (The
    marker a refined method dispatch ends with, which consumers of choices
    already read as no value.) -/
def noValue (p : Pos) : SExpr := .app p (.ident p "$methodMiss") [] false

def isNoValue : SExpr → Bool
  | .app _ (.ident _ "$methodMiss") [] false => true
  | _ => false

/-- Where a cast that refines type arguments, opens them, or goes through
    views is taken (#243, #250, #351), as the refusal of one elsewhere says. -/
def castRefusalNote : String :=
  "only as a clause of a failure context (an if's condition, a for's clauses, a <decides> body, option{…}, …)"

/-- What sets off the place a cast refusal carries: no message has it. -/
def refusalMark : String := "\x01"

/-- A cast refused where it is, which only a failure context's clause may be
    (#243, #250, #351): its place, and whether it opens type arguments,
    which name nothing outside what follows it. -/
structure CastRefusal where
  pos : Pos
  opens : Bool
  deriving Inhabited

/-- The refusal `r`, which an `if`, a `for` or `first{…}` whose clause the
    cast is takes back (`withCastClauses`). The elaborator's errors are
    strings, as `eerr` makes them: this one is its message, then `r` between
    marks, which `castRefusal?` reads, so that what takes it back depends on
    no message's words. `elabProgram` takes `r` off (`unmarked`): a user
    reads the message only. -/
def castRefusal (r : CastRefusal) (msg : String) : String :=
  s!"{r.pos.show}: {msg}{refusalMark}{r.pos.line}:{r.pos.col}:{if r.opens then 1 else 0}:{r.pos.file}{refusalMark}"

/-- The cast refusal an error is (`castRefusal`), if it is one (not one
    whose message another quotes). -/
def castRefusal? (err : String) : Option CastRefusal :=
  match err.splitOn refusalMark with
  | [_, r, ""] => match r.splitOn ":" with
    | line :: col :: opens :: file =>
      match line.toNat?, col.toNat? with
      | some line, some col => some { pos := { line, col, file := ":".intercalate file }, opens := opens == "1" }
      | _, _ => none
    | _ => none
  | _ => none

/-- An error as a user reads it: without the places of cast refusals. -/
def unmarked (err : String) : String :=
  String.join ((err.splitOn refusalMark).zipIdx.filterMap fun (part, i) => if i % 2 == 0 then some part else none)

/-- The expression whose value a branch gives: its last statement's,
    through blocks and `first{…}`. -/
partial def valueOf : SExpr → SExpr
  | .block p ss => (ss.getLast?.map valueOf).getD (.tuple p [])
  | .app p (.ident _ "$first") [.block _ ss] false => (ss.getLast?.map valueOf).getD (.tuple p [])
  | e => e

/-- A clause that casts, as a refining cast would be written: `D := T[X]`,
    or `T[X]`, whose value is then named `$cast…` for its branch. Its
    position, the name, `T` and `X`; an index or a call looks the same, which
    the elaborator tells apart by `T`. -/
def castClause? : SExpr → Option (Pos × String × String × SExpr)
  | .decl p d none false (.app _ (.ident _ T) [x] true) => some (p, d, T, x)
  | .app p (.ident _ T) [x] true => some (p, s!"$cast{p.line}_{p.col}", T, x)
  | _ => none

/-- A cast clause the elaborator made, `$made(D := T[X])`, whose `if`'s
    branch the source does not have as such: its lift carries it
    (`Lift.body`). -/
def made (c : SExpr) : SExpr := .app c.pos (.ident c.pos "$made") [c] false

/-- The clauses of a condition, the first unmarked, and whether it was
    `made`. -/
def unmade : List SExpr → Bool × List SExpr
  | .app _ (.ident _ "$made") [c] false :: cs => (true, c :: cs)
  | cs => (false, cs)

/-- The places of the casts to a class (`isClass`) inside clause `c`, but
    not the one it is (`castClause?`), where the lifting of choices reaches
    (`Choice.liftE`): in the operands it evaluates in order, not in a branch
    of an `if`, a block, nor a failure context of its own. -/
partial def castsIn (isClass : String → Bool) (c : SExpr) : List Pos :=
  let here (e : SExpr) : List Pos := match e with
    | .app q (.ident _ T) [_] true => if isClass T then [q] else []
    | _ => []
  let rec go (e : SExpr) : List Pos := match e with
    | .app _ (.ident _ n) _ _ => if n.startsWith "$" then [] else e.children.flatMap go ++ here e
    | .app .. | .member .. | .bin .. | .cmp .. | .query .. | .neg .. | .tuple .. | .arrayLit ..
    | .str .. | .mapLit .. | .construct .. => e.children.flatMap go ++ here e
    | _ => []
  let inner : SExpr → List Pos := fun x => x.children.flatMap go
  match c with
  | .decl _ _ _ _ v => if (castClause? c).isSome then inner v else go v
  | .set _ _ _ v | .gen _ _ _ v => go v
  | .app .. => if (castClause? c).isSome then inner c else go c
  | e => go e

/-- Clause `c` with the cast at `q` inside it marked to be a clause of its
    own (`$liftCast`), which the lifting of choices then makes it
    (`Choice.liftE`): the operands evaluated before it bound to names first,
    so they still run before it, the cast bound to a name, and `c` with
    that name in its place. -/
def markCast (q : Pos) (c : SExpr) : SExpr :=
  Choice.mapE (fun
    | e@(.app p (.ident _ _) [_] true) => if p == q then some (.app p (.ident p "$liftCast") [e] false) else none
    | _ => none) c

/-- The branch of a refining cast that is the first clause of an `if`'s
    condition, `if (D := T[X], rest) then B else E`: the `if` of the rest,
    `if (rest, true?) then B else E` (the cast has no effects to undo when
    the rest fails; `true?`, which may fail, keeps the rest a condition
    when it cannot fail itself, as the whole condition could). -/
def castRest (p : Pos) (more : List SExpr) (body : SExpr) (els : Option SExpr) : SExpr :=
  if more.isEmpty then body else .ite p (more ++ [.query p (.ident p "true")]) body els

/-- (#243) Clauses `pre, D := T[X], rest` of a failure context (an `if`'s
    condition, a `for`'s clauses, `first{…}`'s) whose cast refines, with the
    code their names reach after them, `after` (the branch, the body, the
    value), when the cast cannot take `after` into its branch, which runs
    outside the failure context (the clauses before it have effects its
    failure must undo; a `for`'s body is not one with its clauses). The cast
    takes the clauses after it, up to the next generator (`isGen`), as its
    branch, in a clause `if (D := T[X]) then first{rest; names} else fail`,
    as a sequence's cast does (`elabSeqIn`), so that their failure, or its
    own, is the clauses': the names they bind that later code uses are its
    value, bound again after it. `after` casts the object again, `if (D :=
    T[X']) then after`, when it uses `D` or a name bound after it, and so
    each cast after it to a class (`isClass`): each succeeds as the first one
    did (an object's class does not change), so that `after` is typed under
    their refinements too. A later cast's object is a local fixed before the
    clauses (`isFixed`), or else one computed among them, bound to a name
    first, which is one of their values, unless it may name type arguments a
    cast among them opens (this one, when it `opens`, or a later one, which
    may): `after` has no name for those. The new clauses and `after`, or why
    not. -/
def castRestClauses (pre : List SExpr) (cast : Pos × String × String × SExpr) (opens : Bool)
    (rest : List SExpr) (after : SExpr) (isGen : SExpr → Bool := fun _ => false)
    (isClass : String → Bool := fun _ => true) (isFixed : String → Bool := fun _ => false) :
    Except String (List SExpr × SExpr) := do
  let (p, d, T, x) := cast
  let branch0 := rest.takeWhile (!isGen ·)
  let later := rest.dropWhile (!isGen ·)
  let usedLater := Choice.namesUsed (.block p later)
  if usedLater.contains d then
    throw s!"a clause after it, past a generator or a choice, uses {d}"
  let usedAfter := Choice.namesUsed after
  let obj (q : Pos) : String := s!"$castObj{q.line}_{q.col}"
  let castOf (q : Pos) (e T : String) (y : SExpr) : SExpr := .decl q e none false (.app q (.ident q T) [y] true)
  -- (the later casts' objects to cast again, and the names whose values may
  -- name opened type arguments: what casts bind, and what uses those)
  let (objs, branch, _) := branch0.foldl (fun (objs, cs, tainted) c => match c with
    | .decl q e none false (.app _ (.ident _ T') [x'] true) =>
      let mayName := (Choice.namesUsed x').any tainted.contains
      if !isClass T' then (objs, cs ++ [c], if mayName then tainted ++ [e] else tainted)
      else if let .ident _ n := x' then
        if isFixed n then (objs ++ [(e, T', x', none)], cs ++ [c], tainted ++ [e])
        else if mayName then (objs, cs ++ [c], tainted ++ [e])
        else (objs ++ [(e, T', .ident q (obj q), some (obj q))], cs ++ [.decl q (obj q) none false x', castOf q e T' (.ident q (obj q))], tainted ++ [e])
      else if mayName then (objs, cs ++ [c], tainted ++ [e])
      else (objs ++ [(e, T', .ident q (obj q), some (obj q))], cs ++ [.decl q (obj q) none false x', castOf q e T' (.ident q (obj q))], tainted ++ [e])
    | .decl _ n _ _ v => (objs, cs ++ [c], if (Choice.namesUsed v).any tainted.contains then tainted ++ [n] else tainted)
    | c => (objs, cs ++ [c], tainted)) (([] : List (String × String × SExpr × Option String)), ([] : List SExpr), if opens then [d] else [])
  -- (the casts `after` casts again, each when it uses its name or one bound
  -- after it, and no clause past a generator does: this one, of its object
  -- bound once, and those after it)
  let names (cs : List SExpr) : List String := cs.filterMap fun | .decl _ n _ _ _ => some n | _ => none
  let rec fromCast (e : String) : List SExpr → List SExpr
    | [] => []
    | c@(.decl _ n _ _ _) :: cs => if n == e then c :: cs else fromCast e cs
    | _ :: cs => fromCast e cs
  let again := ((d, T, .ident p (obj p), none) :: objs).filter fun (e, _) =>
    !usedLater.contains e && (e :: names (if e == d then branch else fromCast e branch)).any usedAfter.contains
  let kept : List (String × Bool) := branch.filterMap fun
    | .decl _ n _ v _ =>
      if again.any (·.1 == n) then none
      else if (usedLater ++ usedAfter).contains n || again.any (·.2.2.2 == some n) then some (n, v)
      else none
    | _ => none
  let vals := s!"$castVals{p.line}_{p.col}"
  let value : SExpr := match kept with
    | [(n, _)] => .ident p n
    | ns => .tuple p (ns.map fun (n, _) => .ident p n)
  let headAgain := again.any (·.1 == d)
  let tail := SExpr.ite p [made (castOf p d T (if headAgain then .ident p (obj p) else x))]
    (.app p (.ident p "$first") [.block p (branch ++ [value])] false) (some (noValue p))
  let get (i : Nat) : SExpr := if kept.length == 1 then .ident p vals else .app p (.ident p vals) [.int p (i : Int)] false
  let clauses := pre ++ (if headAgain then [.decl p (obj p) none false x] else []) ++
    (if kept.isEmpty then [tail] else
      .decl p vals none false tail :: kept.zipIdx.map fun ((n, v), i) => .decl p n none v (get i)) ++ later
  -- (at `after`'s place: the first casts are at the casts' own)
  let q := after.pos
  let after := again.foldr (fun (e, T', y, _) acc =>
    .ite q [made (castOf q e T' y)] acc (some (.app q (.ident q "Err") [] false))) after
  return (clauses, after)

/-- The branches the lifts ask for, as functions: each `if (D := …) then
    Body …` whose position and bound name are a lift's key gives `Body`,
    with the refinement applied to its written types. Found anywhere in the
    program, also in a branch that is lifted itself. -/
def functions (lifts : List Lift) (tops : List STop) : List STop := Id.run do
  if lifts.isEmpty then return []
  let mut out : Array STop := #[]
  let mut done : List String := []
  -- (a branch the lift has, a method's or one the elaborator made, as it is)
  for l in lifts do
    if let some b := l.body then
      done := l.key :: done
      out := out.push (.fn l.pos l.name l.params l.tparams l.specs l.ret (substTypes l.subst b))
  let mut todo : List SExpr := tops.flatMap fun
    | .fn _ _ ps _ _ _ b => b :: ps.filterMap (·.default)
    | .classDef _ _ _ _ _ _ _ _ ms => ms.flatMap fun
        | .fn _ _ ps _ _ _ b => b :: ps.filterMap (·.default)
        | _ => []
    | _ => []
  while !todo.isEmpty do
    let e := todo.head!
    todo := todo.tail!
    if let .ite p [.decl _ d none false _] body _ := e then
      if let some l := lifts.find? (·.key == keyOf p d) then
        if !done.contains l.key then
          done := l.key :: done
          out := out.push (.fn p l.name l.params l.tparams l.specs l.ret (substTypes l.subst body))
    todo := e.children ++ todo
  return out.toList

end OpenVerse.Front.Refine
