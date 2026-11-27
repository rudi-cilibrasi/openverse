/-
  OpenVerse front end — choice `a₁ | a₂ | …` (#208), its surface side.

  A choice is parsed as `$choice(a₁, a₂, …)`, an `.app` of a reserved name
  (as `$branch` and `$defer` are), with the alternatives that are choices
  themselves spliced in: `(1 | 2) | 3` is `1 | 2 | 3`.

  A choice has several values (the Verse Calculus's), taken by the nearest
  failure context: all of them by the clauses of a `for`, the first success
  by an `if` condition and by `first{…}`. For now a choice can be the value
  of a binding there (`X := a | b`, `X:t = a | b`), or a clause of its own;
  `normClauses` makes each of those a binding, which the elaborator compiles
  with `Expr.altE`, `Expr.chooseFirst` and `Expr.firstE` (Core/Derived.lean,
  where their behaviour is proved).
-/
import OpenVerse.Front.Syntax
import OpenVerse.Front.MethodOverloads

namespace OpenVerse.Front.Choice

/-- The alternatives of a choice. -/
def alts? : SExpr → Option (List SExpr)
  | .app _ (.ident _ "$choice") as false => some as
  | _ => none

def isChoice (e : SExpr) : Bool := (alts? e).isSome

/-- `a₁ | a₂ | …`, with the alternatives that are choices spliced in. -/
def mk (p : Pos) (as : List SExpr) : SExpr :=
  .app p (.ident p "$choice") (as.flatMap fun a => (alts? a).getD [a]) false

/-- A binding of a choice, the form the elaborator compiles. -/
structure Binding where
  pos : Pos
  name : String
  /-- The written type. -/
  ty : Option STy
  alts : List SExpr
  /-- For `set L = a | b`: `L`, at whose type the alternatives are taken. -/
  place : Option SExpr := none
  /-- For an `if` with choices in its branches (#235): the `if`, whose
      branches' alternatives the elaborator guards by the branch taken. -/
  branchy : Option SExpr := none
  /-- For a call of a recursive function with several values (#235): the
      array of its values, `F$all(args)`; the binding takes each in turn.
      Or, for one taken lazily (#246), the call `$loop(F, …)`, whose
      consumer takes its values one at a time. -/
  each : Option SExpr := none

def binding? : SExpr → Option Binding
  | .decl p x ty false (.app _ (.ident _ "$choice") as false) => some ⟨p, x, ty, as, none, none, none⟩
  | .decl p x ty false (.app _ (.ident _ "$choiceAt") (l :: as) false) => some ⟨p, x, ty, as, some l, none, none⟩
  | .decl p x ty false (.app _ (.ident _ "$branchChoice") [i] false) => some ⟨p, x, ty, [], none, some i, none⟩
  | .decl p x ty false (.app _ (.ident _ "$branchChoiceAt") [l, i] false) => some ⟨p, x, ty, [], some l, some i, none⟩
  | .decl p x ty false (.app _ (.ident _ "$each") [a] false) => some ⟨p, x, ty, [], none, none, some a⟩
  | .decl p x ty false e@(.app _ (.ident _ "$loop") _ false) => some ⟨p, x, ty, [], none, none, some e⟩
  | .decl p x ty false e@(.app _ (.ident _ "$choiceProducer") _ false) => some ⟨p, x, ty, [], none, none, some e⟩
  | _ => none

/-- An `if … else …` with a choice in a branch (the branches of an `else if`
    chain included): it has the values of the branch its conditions pick. -/
partial def isBranchy : SExpr → Bool
  | i@(.ite _ _ t (some e)) => complete i && (isChoice t || isChoice e || isBranchy t || isBranchy e)
  | _ => false
where
  /-- Every `else if` of the chain has an `else`. -/
  complete : SExpr → Bool
    | .ite _ _ _ (some e@(.ite ..)) => complete e
    | .ite _ _ _ (some _) => true
    | _ => false

/-- The branches of an `if … else if … else …` chain: each one's conditions
    (none for the last `else`) and its expression. A missing `else` gives
    one void value. -/
partial def arms : SExpr → List (Option (List SExpr) × SExpr)
  | .ite _ cs t (some e) => (some cs, t) :: arms e
  | .ite p cs t none => [(some cs, t), (none, .tuple p [])]
  | e => [(none, e)]

/-- Supply the implicit void arm of an incomplete `if` chain. -/
partial def fillElse (e : SExpr) : SExpr :=
  match e with
  | .ite p cs t u => .ite p cs t (some ((u.map fillElse).getD (.tuple p [])))
  | _ => e

/-- The part of a made name that names an inlined call's site (#235), set
    apart from the position after it (site 1 at line 12 is not site 11 at
    line 2); nothing outside one. -/
def sitePart (site : String) : String :=
  if site.isEmpty then "" else
    -- First-success lowering reuses a renamed result as its next site.
    -- Bound that prefix before it is added to more renamed locals.
    (if site.utf8ByteSize <= 256 then site else s!"$site{site.hash}") ++ "@"

/-- The name made for what is bound of kind `k` from `p` (`$c12_5` for a
    choice at 12:5), with an inlined call's `site` in it (`sitePart`). -/
def madeName (k site : String) (p : Pos) : String := s!"${k}{sitePart site}{p.line}_{p.col}"

/-- (#283) An `if` with something
    to lift in a branch that `isBranchy` leaves there: a call with several
    values, or a choice inside a branch's expression (`has`, `hasLiftable`,
    says which). Each branch is lifted in its own path of an exclusive
    choice (#314, #331); a block as a branch has its names renamed for it
    where it is lifted (`bifToExcl`), its `defer:`s after its value
    (`deferLast`), as any block's. -/
def branchesLift (has : SExpr → Bool) (e : SExpr) : Bool :=
  match e with
  | .ite .. => (arms e).any fun (_, v) => has v
  | _ => false

/-- (#283) Whether the elaborator takes this `if` with choices in its
    branches as it is (`elabBranchAlts`): each branch a value or a choice
    of values with nothing to lift. -/
def plainBranches (has : SExpr → Bool) (e : SExpr) : Bool :=
  isBranchy e && (arms e).all fun (_, v) => match alts? v with
    | some xs => !xs.any has
    | none => !has v

/-- The indices of a `set` path bound to names, in order (unless literals),
    and the path with those names in their places: `set` evaluates them
    before the new value. -/
partial def hoistPath (q : Pos) (l : SExpr) (site : String := "") : List SExpr × SExpr :=
  let nm (n : Nat) : String := s!"{madeName "i" site q}_{n}"
  let rec go (n : Nat) : SExpr → List SExpr × SExpr × Nat
    | .app r base args true =>
      let (h, base', n) := go n base
      let (h2, args', n) := args.foldl (fun (h, acc, n) a => match a with
        | .int .. | .char .. | .char32 .. => (h, acc ++ [a], n)
        | a => (h ++ [.decl r (nm n) none false a], acc ++ [.ident r (nm n)], n + 1)) (h, [], n)
      (h2, .app r base' args' true, n)
    | .member r base f =>
      let (h, base', n) := go n base
      (h, .member r base' f, n)
    | .query r base =>
      let (h, base', n) := go n base
      (h, .query r base', n)
    | e => ([], e, n)
  let (h, l', _) := go 0 l
  (h, l')

/-- `set L op= R` whose `R` needs code before it (a choice, or lifted
    operands): `L`'s indices, then that code, as `set` evaluates; for `op=`
    the old value is read after it, by the `set` itself (the Book of Verse's
    tests, `ArrayAppend.versetest` 140, 183: the new value first). The
    result: the clauses before, the old value's name (none: `$withOld(O, R)`,
    which told the elaborator that the old value was already in `O`, is no
    longer made here), and the path. -/
def setPrefix (q : Pos) (l : SExpr) (_op : Option String) (site : String := "") :
    List SExpr × Option String × SExpr :=
  let (h, l') := hoistPath q l site
  (h, none, l')

/-- The new value of a `set` whose old one is in `o?`. -/
def withOld (q : Pos) (o? : Option String) (r : SExpr) : SExpr :=
  match o? with
  | some o => .app q (.ident q "$withOld") [.ident q o, r] false
  | none => r

/-! ### A choice inside an expression

A choice in an operand is lifted out of its clause (A-normal form): the
operands evaluated before it are bound to fresh names first, so that they
still run once and before it, then the choice itself, and the clause keeps
the choice's name in its place:

    X := F() + (1 | 2)    ⟶    $t := F(), $c := 1 | 2, X := $t + $c

Lifting goes through the operands that are evaluated left to right, once
each: those of arithmetic, comparisons, calls (the receiver first), member
access, `?`, tuples, arrays, maps and string interpolation; a call's
named arguments after its positional ones, as they are evaluated; a
block's clauses; a construction's fields, as they are evaluated (those
given in the order written, #724); a range's bounds; the operands of `and`, each as a
block, and the right of `or`, as the `if` it stands for (`orIf`) (#283). A
choice elsewhere (a branch that is more than a value, an alternative, which
the elaborator takes apart) is not lifted here. -/

/-- The variable a `set` path starts from. -/
partial def rootName? : SExpr → Option String
  | .ident _ n => some n
  | .member _ e _ | .app _ e _ true | .query _ e => rootName? e
  | _ => none

/-- The names that `set` writes inside `e`. -/
partial def setsIn (e : SExpr) : List String :=
  let here := match e with
    | .set _ l _ _ => (rootName? l).toList
    | _ => []
  here ++ e.children.flatMap setsIn

/-- The names a clause list binds (so values, for `stable` and the heads
    of calls). -/
def boundIn (cs : List SExpr) : List String := Id.run do
  let mut depth := 0
  let mut names := []
  for clause in cs do
    match clause with
    | .app _ (.ident _ "$producerAnchorStart") [_] false
      | .app _ (.ident _ "$producerFrameStart") [] false => depth := depth + 1
    | .app _ (.ident _ "$producerAnchorEnd") [_] false
      | .app _ (.ident _ "$producerFrameEnd") [] false => depth := depth - 1
    | _ =>
      if depth != 0 then continue
      names := names ++ match clause with
        | .decl _ x _ _ _ => [x]
        | .gen _ x i _ => x :: i.toList
        -- An inlined generic call's omitted defaults are bound together.
        | .app _ (.ident _ "$defaults") (.block _ ds :: _) false => ds.filterMap fun
            | .decl _ x _ _ _ => some x
            | _ => none
        | _ => []
  return names

/-- The receiver of a method or field. -/
def recvOf : SExpr → SExpr
  | .member _ obj _ => obj
  | e => e

/-- What a call's head evaluates before its arguments, as operands: a head
    that is a value (a variable holding an array, a map or a function, `isVal`
    says which names are), the receiver of a method or field (unless a
    module, class or other name that is no value), or any other expression;
    not a function's or class's name. -/
def headOps (isVal : String → Bool) (isField : String → String → Bool) : SExpr → List SExpr × Bool
  | f@(.ident _ n) => if isVal n then ([f], true) else ([], true)
  -- (a field holding an array, map or function is read whole, first; a
  -- method's receiver only)
  | f@(.member _ (.ident _ n) m) =>
    if isField n m then ([f], true) else if isVal n then ([recvOf f], false) else ([], false)
  | f@(.member _ _ _) => ([recvOf f], false)
  | f => ([f], true)


/-- Whether a call's head has a choice that lifting reaches. -/
partial def headHas (hasL : SExpr → Bool) : SExpr → Bool
  | .ident .. => false
  | .member _ obj _ => hasL obj
  | f => hasL f


/-- `e` kept where it is, with a choice inside that is not lifted, and why,
    for the elaborator's message (#283). -/
def noLift (p : Pos) (why : String) (e : SExpr) : SExpr :=
  .app p (.ident p "$noLift") [.str p [.text why], e] false

/-- A name as written: one renamed for a place (a block's local, #283) is
    `$…'N`. -/
def shownName (n : String) : String :=
  if n.startsWith "$" && n.contains '\'' then ((n.splitOn "'").getLast?.getD n) else n

/-- The parser's `first` range producer, with a way to replace its bounds.
    An explicitly written `for` remains a scope of its own. -/
def firstRangeBounds? : SExpr → Option (SExpr × SExpr × (SExpr → SExpr → SExpr))
  | .app p f@(.ident _ "$each")
      [.forE q [.decl r n none false (.range b lo hi)] v@(.ident _ result)] false =>
    if n == result && (shownName n).startsWith "$firstRange" then
      some (lo, hi, fun lo hi => .app p f [.forE q [.decl r n none false (.range b lo hi)] v] false)
    else none
  | _ => none

/-- The names `ns` renamed for a place, `tag'N` (`tag` a made name, so
    `shownName` gives `N` back), so they stay its own there. -/
def renamedFor (tag : String) (ns : List String) : List (String × String) :=
  ns.map fun n => (n, s!"{tag}'{n}")

/-- Whether a `set` path's indices have something to lift (`has`,
    `hasLiftable`), #283: a choice, or a call with several values. -/
partial def pathHas (has : SExpr → Bool) : SExpr → Bool
  | .app _ base args true => pathHas has base || args.any has
  | .member _ base _ | .query _ base => pathHas has base
  | _ => false

/-- An exclusive selection already normalized inside a value block still
    needs that block lifted into its consumer. Its own declaration remains
    exclusive, so the consumer adds no generator at the selection boundary. -/
private partial def blockHasExclusive : SExpr → Bool
  | .app _ (.ident _ "$excl") _ false => true
  | .block _ ss => ss.any blockHasExclusive
  | .decl _ _ _ _ value => blockHasExclusive value
  | .ite _ _ t u => blockHasExclusive t || u.any blockHasExclusive
  | _ => false

mutual
/-- Whether `e` has a choice that lifting reaches. -/
partial def hasLiftable : SExpr → Bool
  -- (a block or construction kept, with why, `$noLift`, #283)
  | .app _ (.ident _ "$noLift") _ false => false
  -- (an inlined function's parameter default, in its own context, #283)
  | .app _ (.ident _ "$paramDefault") _ false => false
  | .app _ (.ident _ "$constructProbe") _ false => false
  | .app _ (.ident _ "$mapKeySources") [_, value] false => hasLiftable value
  -- (an exclusive choice, which a `for` compiles itself, #314)
  | .app _ (.ident _ "$excl") _ false => false
  | .app _ (.ident _ "$choice") _ false => true
  -- (a cast that only a failure context's clause may be, #243, marked so
  -- by the elaborator: lifted to be one)
  | .app _ (.ident _ "$liftCast") _ false => true
  | .app _ (.ident _ "$inline") _ false => true
  -- (an overridden method's dispatch, which becomes an inlined call, #283)
  | .app _ (.ident _ "$dispatch") _ false => true
  | .app _ (.ident _ "$each") _ false => true
  | .app _ (.ident _ "$loop") _ false => true
  | .app _ (.ident _ "$choiceProducer") _ false => true
  -- (#283) a call of a lazily taken group, in its own code (`markPoints`)
  | .app _ (.ident _ "$point") _ false => true
  -- (a scope's `defer:`s pending for the exits in `e`, `deferExits`, #283)
  | .app _ (.ident _ "$deferExits") [_, e] false => hasLiftable e
  | e@(.ite ..) => isBranchy e || branchesLift hasLiftable e
  | .app _ f args _ => headHas hasLiftable f || args.any fun
      -- (a named argument's value, #283)
      | .decl _ n _ _ x => n.startsWith "?" && hasLiftable x
      -- (the body of `first{…}`, `spawn`, `branch`, `defer`, `sync`, … is
      -- no value to lift from: its choices are its own)
      | a@(.block ..) => !(match f with | .ident _ n => n.startsWith "$" | _ => false) && hasLiftable a
      | a => hasLiftable a
  -- (operands evaluated left to right, once each)
  | e@(.bin ..) | e@(.range ..) | e@(.cmp ..) | e@(.member ..) | e@(.query ..) | e@(.neg ..)
  | e@(.tuple ..) | e@(.arrayLit ..) | e@(.str ..) | e@(.mapLit ..) => e.children.any hasLiftable
  -- (#283) the operands of `and`, and the right of `or` (its left is a
  -- failure context, which takes its own): each a clause, of a scope of its own
  | .andE _ a b => liftsHere a || liftsHere b
  | .orE _ _ b => liftsHere b
  -- (a construction's field values and a block's clauses, #283)
  | .construct _ _ _ fs => fs.any fun | .decl _ _ _ _ x => hasLiftable x | x => hasLiftable x
  | .set _ path _ value => pathHas hasLiftable path || hasLiftable value
  | .block _ ss => ss.any liftsHere || ss.any blockHasExclusive
  -- (#283) a `case`'s scrutinee and arms, as the `if` chain that selects its
  -- arm is lifted (`caseIf`)
  | .caseE _ x arms => hasLiftable x || arms.any fun (_, a) => hasLiftable a
  | _ => false

/-- A clause with something to lift into the clauses it is among: in a
    binding's value or a generator's source, in a `set`'s value or path, or
    in the clause itself. -/
partial def liftsHere : SExpr → Bool
  | .decl _ _ _ _ x | .gen _ _ _ x => hasLiftable x
  | .set _ l _ x => hasLiftable x || pathHas hasLiftable l
  | x => hasLiftable x
end

/-- An `if` that can lift directly at the binding's expected type.
    An incomplete chain first needs a binding of its own at void. -/
def liftsAsIf (e : SExpr) : Bool :=
  isBranchy.complete e && (isBranchy e || branchesLift hasLiftable e)

/-- (#283) A composed choice: one whose alternatives have values or clauses
    of their own to lift, so that each alternative is taken with the
    clauses after it (`elabOneGo`, `elabForWith`). -/
def Binding.composed (b : Binding) : Bool :=
  b.place.isNone && b.branchy.isNone && b.each.isNone && b.alts.any hasLiftable

/-- (#283) `A or B` with something to lift on its right, as the `if` it
    stands for, `if (T := A) then T else B`: its condition takes the first
    success of `A`, as the left of `or` does, and its values are otherwise
    `B`'s; each operand a block, a scope of its own. Lifted as any `if` with
    choices in its branches is, at a binding's or `set`'s place too. -/
def orIf (site : String) : SExpr → SExpr
  | e@(.orE p a b) =>
    if !liftsHere b then e else
    let t := madeName "or" site p
    .ite p [.decl p t none false (.block a.pos [a])] (.ident p t) (some (.block b.pos [b]))
  | e => e

/-- `set L op= a | b` with the choice bound first, as `set` evaluates (Book
    of Verse §3.5): the indices of `L`'s path, then the choice, so each
    alternative only runs the assignment (for `op=`, reading the old value
    as it is then). For `=`,
    the alternatives take `L`'s type; when one has something to lift (#283),
    by each running the assignment itself, the `set` its block's value, as
    a composed choice's alternatives are lifted one by one. -/
def setClauses (p : Pos) (l : SExpr) (op : Option String) (as : List SExpr) (site : String := "") :
    List SExpr × SExpr :=
  let (h, o?, l') := setPrefix p l op site
  let c := madeName "c" site p
  match op with
  | none =>
    if as.any hasLiftable then
      (h ++ [.decl p c none false (.app p (.ident p "$choice") (as.map fun a => .block a.pos [.set p l' none a]) false)],
        .ident p c)
    else (h ++ [.decl p c none false (.app p (.ident p "$choiceAt") (l' :: as) false)], .set p l' none (.ident p c))
  | some _ => (h ++ [.decl p c none false (.app p (.ident p "$choice") as false)], .set p l' op (withOld p o? (.ident p c)))

/-- The clauses, with each choice the value of a binding: a clause that is a
    choice gets a name of its own, and `set L = a | b` and `var X:t = a | b`
    bind the choice first. -/
def normClauses (cs : List SExpr) (site : String := "") : List SExpr :=
  cs.flatMap fun c =>
    let nm (p : Pos) : String := madeName "c" site p
    match c with
    | .app p (.ident _ "$choice") _ false => [.decl p (nm p) none false c]
    | .set p l op rhs => match alts? rhs with
      | some as => let (h, s) := setClauses p l op as site; h ++ [s]
      | none => [c]
    | .decl p x ty true rhs =>
      if isChoice rhs then [.decl p (nm p) ty false rhs, .decl p x ty true (.ident p (nm p))] else [c]
    -- (`set L = a | b` as the last clause of a macro, which names its value)
    | .decl p x ty false (.set q l op rhs) => match alts? rhs with
      | some as => let (h, s) := setClauses q l op as site; h ++ [.decl p x ty false s]
      | none => [c]
    | c => [c]

/-- The same whenever evaluated, and typed by where they are (so they keep
    their expected type in place), so not bound to a name of their own:
    literals, `array{}`, `map{}`, and names that are no values (functions,
    classes, enumerators, `true`, `false`). Not names of values: a bare name
    may be a variable an alternative sets, or a field of `Self` that its
    method call changes. -/
partial def stable (isVal : String → Bool) : SExpr → Bool
  | .int .. | .char .. | .char32 .. | .float .. => true
  | .neg _ e => stable isVal e
  | .str _ ps => ps.all fun | .text _ => true | .code _ => false
  | .arrayLit _ es | .tuple _ es => es.all (stable isVal)
  | .mapLit _ kvs => kvs.all fun (k, v) => stable isVal k && stable isVal v
  | .optionLit _ (.block _ [e]) => stable isVal e
  | .ident _ n => !isVal n
  | .member _ (.ident _ n) _ => !isVal n
  | _ => false

/-- Construction metadata supplied by the elaborator. A discarded type
    probe keeps the construction whole so every field retains its expected type. -/
structure FieldOrder where
  fields : List (String × Bool) := []
  probe : Bool := false
  inlineSite : String := ""
  origin : String := ""
  hints : List SExpr := []

structure LiftSt where
  next : Nat := 0
  /-- The clauses lifted so far, in order. -/
  pre : Array SExpr := #[]
  /-- Part of every name made: the call site of the function being inlined
      (#235), so two calls of one function do not make the same names. -/
  site : String := ""
  inlineSite : String := ""
  /-- A struct's or class's fields in declaration order, the order its
      constructions evaluate them in, each with whether it has a default
      that is more than a literal (so runs where it is, #283); `[]` when not
      known here. -/
  fieldOrder : String → FieldOrder := fun _ => {}

abbrev LM := StateM LiftSt

def LM.fresh (p : Pos) (k : String) : LM String :=
  modifyGet fun s => (s!"{madeName k s.site p}_{s.next}", { s with next := s.next + 1 })

/-- Add `c` to the clauses lifted so far. -/
def LM.push (c : SExpr) : LM Unit :=
  modify fun s => { s with pre := s.pre.push c }

def LM.bind (p : Pos) (k : String) (e : SExpr) (ty : Option STy := none) : LM SExpr := do
  let x ← LM.fresh p k
  LM.push (.decl p x ty false e)
  return .ident p x

/-- `e` with `go` applied to each subexpression a rewrite descends into:
    its `children`, except that a construction's field bindings give their
    values only (so field names are kept), and a struct's field defaults
    too. -/
def descendM [Monad m] (go : SExpr → m SExpr) : SExpr → m SExpr
  | .construct p n ts fs => return .construct p n ts (← fs.mapM fun
      | .decl q fn t v x => do return .decl q fn t v (← go x)
      | a => go a)
  | .structDef p tps specs fs => return .structDef p tps specs (← fs.mapM fun f => do return { f with default := ← f.default.mapM go })
  | e => e.mapChildrenM go

/-- `e` with `f` applied top-down: where `f` gives a replacement, it is used
    (and not descended into); elsewhere `descendM` goes on. -/
partial def mapE (f : SExpr → Option SExpr) (e : SExpr) : SExpr :=
  match f e with
  | some e' => e'
  | none => Id.run (descendM (m := Id) (mapE f) e)

/-- A raw producer adapter is inlined before its original call defaults are
    prepared. Restore caller flags on those parameter-default nodes only;
    wrapping the entire expanded producer would move its scope markers. -/
partial def restoreProducerDefaultContexts (expression : SExpr) : SExpr :=
  mapE (fun
    | .app p (.ident _ "$producerDefaultContext")
        [.str _ [.text function], stack, flags, value] false =>
      let value := restoreProducerDefaultContexts value
      some (mapE (fun
        | node@(.app q (.ident _ "$paramDefault") (.ident _ owner :: _) false) =>
          if owner == function || owner == function ++ "$fam" then
            some (.app q (.ident p "$defaultContext") [stack, flags, node] false)
          else none
        | _ => none) value)
    | _ => none) expression

/-- An exclusive choice (#314): at most one alternative's `guards` hold,
    and that alternative's value is its `rest`'s (a block). A `for`
    compiles it as the `if` it stands for, with no generator, so that what
    came before it rolls back as it would without it. Elsewhere it is the
    choice of `block{guards; rest}`. -/
def mkExcl (p : Pos) (alts : List (List SExpr × SExpr)) : SExpr :=
  .app p (.ident p "$excl") (alts.map fun (gs, r) => .app p (.ident p "$alt") [.block p gs, r] false) false

/-- `if (cs) then t else u` as an exclusive choice of its two branches
    (#314), its conditions taken once, first, by the binding of `k` that
    comes with it: with no names bound, `k := if (cs) then 0 else 1`, each
    branch guarded by `k = 0` or `k = 1`; otherwise `k := option{cs; the
    names}`, the then branch's guards binding the names again from `k?`
    (each with its written type, a `var` still one), the else branch's
    `not k?`. -/
def exclOfIf (p : Pos) (k : String) (cs : List SExpr) (t u : SExpr) : SExpr × SExpr :=
  match boundIn cs with
  | [] =>
    let g (i : Int) : List SExpr := [.cmp p (.ident p k) [("=", .int p i)]]
    (.decl p k none false (.ite p cs (.int p 0) (some (.int p 1))), mkExcl p [(g 0, t), (g 1, u)])
  | names =>
    let declOf (y : String) : Option STy × Bool :=
      (cs.findSome? fun | .decl _ x yt m _ => if x == y then some (yt, m) else none | _ => none).getD (none, false)
    let (val, binds) : SExpr × List SExpr := match names with
      | [y] => let (yt, m) := declOf y; (.ident p y, [.decl p y yt m (.query p (.ident p k))])
      | ys =>
        let tt := k ++ "t"
        (.tuple p (ys.map (SExpr.ident p ·)),
          .decl p tt none false (.query p (.ident p k)) ::
            ys.zipIdx.map fun (y, i) =>
              let (yt, m) := declOf y
              SExpr.decl p y yt m (.app p (.ident p tt) [.int p (i : Int)] false))
    (.decl p k none false (.optionLit p (.block p (cs ++ [val]))),
      mkExcl p [(binds, t), ([.notE p (.query p (.ident p k))], u)])

/-- The `$joinOf` that goes with the choice of an `if`'s branches when no
    type is written (`bifToExcl`): the `if`, and for `set L = if …` the
    place `L`, from which the elaborator types the choice at the branches'
    join. Not an alternative. -/
def isJoinOf : SExpr → Bool
  | .app _ (.ident _ "$joinOf") _ _ => true
  | _ => false

/-- The `if` and place of the `$joinOf` among a choice's alternatives. -/
def joinOf? (as : List SExpr) : Option (SExpr × Option SExpr) :=
  as.findSome? fun | .app _ (.ident _ "$joinOf") (i :: l) false => some (i, l.head?) | _ => none

/-- `e` with its exclusive choices as choices (#314). Not inside a nested
    `for`, unless `deep`: its own clauses keep theirs, for it to compile as
    `if`s (`deep`, for an effect-free body, where a choice is as exact). -/
partial def exclToChoice (e : SExpr) (deep : Bool := false) : SExpr :=
  let go := fun x => exclToChoice x deep
  mapE (fun
    | f@(.forE ..) => if deep then none else some f
    | .app p (.ident q "$excl") alts false =>
      let alts := alts.filter (!isJoinOf ·)
      some (.app p (.ident q "$choice") (alts.map fun
        | .app _ (.ident _ "$alt") [.block bp gs, .block _ rs] false => .block bp ((gs ++ rs).map go)
        | .app _ (.ident _ "$alt") [.block bp gs, r] false => .block bp (gs.map go ++ [go r])
        | a => a) false)
    | _ => none) e

/-- Whether `e` or a subexpression of it (`SExpr.children`, at any depth)
    satisfies `pr`. -/
partial def anyE (pr : SExpr → Bool) (e : SExpr) : Bool :=
  pr e || e.children.any (anyE pr)

/-- Whether `e` has a `return` in it. -/
partial def hasReturn : SExpr → Bool
  | .app _ (.ident _ "$returnBoundary") _ false => false
  | .ret .. => true
  | e => e.children.any hasReturn

/-- The statements of a body. -/
def stmtsOf : SExpr → List SExpr
  | .block _ ss => ss
  | e => [e]

/-- (#283) A `case` as the `if` chain that selects its arm, where its arms
    are taken apart (a `return` in one, a choice to lift): the arm picked by
    its number first, `k := case (e) { p₀ => 0,
    p₁ => 1, … }` (the same patterns, so the same failure when none matches),
    then `if (k = 0) then a₀ else if (k = 1) then a₁ … else aₙ`. None when its
    scrutinee has a `return`. -/
def caseIf (k : String) : SExpr → Option (SExpr × SExpr)
  | .caseE p e arms => do
    guard (!hasReturn e)
    let (_, lastArm) ← arms.getLast?
    let sel := SExpr.decl p k none false (.caseE p e (arms.zipIdx.map fun ((pat, _), i) => (pat, .int p i)))
    -- (each `if` at its arm's place, so names made for it are its own)
    let chain := (arms.dropLast.zipIdx).foldr (fun ((_, a), i) acc =>
      let q := a.pos
      SExpr.ite q [.cmp q (.ident q k) [("=", .int q i)]] a (some acc)) lastArm
    return (sel, chain)
  | _ => none

/-- Calls of the functions `mv` as `$inline` markers with an empty template:
    enough to see whether a body has several values. -/
def markCalls (mv : List String) : SExpr → SExpr :=
  mapE fun
    | .app p (.ident q g) as _ =>
      if mv.contains g then some (.app p (.ident p "$inline") (.ident q g :: .block p [] :: as) false)
      else none
    | _ => none

/-- The names a body binds (its locals), each where it is bound, struct
    fields and named arguments aside. -/
partial def localDecls : SExpr → List (String × Pos)
  | .app _ (.ident _ "$constructHints") _ false => []
  | .decl p n _ _ x => (if n.startsWith "?" then [] else [(n, p)]) ++ localDecls x
  | .gen p x i src => (x :: i.toList).map (·, p) ++ localDecls src
  -- (a construction's field bindings name its fields)
  | .construct _ _ _ fs => fs.flatMap fun | .decl _ _ _ _ x => localDecls x | a => localDecls a
  | e => e.children.flatMap localDecls

/-- The names `e` binds, at any depth. -/
partial def localsOf (e : SExpr) : List String :=
  ((localDecls e).map (·.1)).eraseDups

/-- (#283) `$declNames` of the names `ds` that a scope moved elsewhere
    declares, each where it does: as written, they are not in scope where
    the scope is, as for its own (Verse has no shadowing); nothing for no
    names. -/
def declNames (p : Pos) (ds : List (String × Pos)) : List SExpr :=
  if ds.isEmpty then [] else [.app p (.ident p "$declNames") (ds.map fun (n, q) => .ident q n) false]

/-- The names an `if`'s conditions `cs` bind (`boundIn`), each where a
    binding binds it (`p` otherwise). -/
def condDecls (p : Pos) (cs : List SExpr) : List (String × Pos) :=
  (boundIn cs).map fun n =>
    (n, (cs.findSome? fun | .decl q x _ _ _ => if x == n then some q else none | _ => none).getD p)

/-- `$shadows` of the first name of `names` (its condition's) that the
    branch `t` binds too: shadowing, said where the branch binds it (#383's
    review); nothing when there is none. -/
def shadowsIn (p : Pos) (names : List String) (t : SExpr) : List SExpr :=
  match (localDecls t).find? fun (n, _) => names.contains n with
  | some (n, q) => [.app p (.ident p "$shadows") [.ident q n] false]
  | none => []

/-- Rename value references embedded in generated method-result types. -/
partial def renameValueTypes (ren : List (String × String)) : STy → STy
  | .app "$methodResult" [.name n] => .app "$methodResult" [.name ((ren.lookup n).getD n)]
  | .arr t => .arr (renameValueTypes ren t)
  | .opt t => .opt (renameValueTypes ren t)
  | .tup ts => .tup (ts.map (renameValueTypes ren))
  | .map k v => .map (renameValueTypes ren k) (renameValueTypes ren v)
  | .app n ts => .app n (ts.map (renameValueTypes ren))
  | .fn ps fx r => .fn (ps.map (renameValueTypes ren)) fx (renameValueTypes ren r)
  | t => t

/-- `e` with the names in `ren` renamed, binders and uses. -/
partial def renameE (ren : List (String × String)) : SExpr → SExpr :=
  mapE fun
    | .ident p n => (ren.lookup n).map (.ident p ·)
    | .decl p n t v x => some (.decl p ((ren.lookup n).getD n) (t.map (renameValueTypes ren)) v (renameE ren x))
    | .gen p x i src => if (ren.lookup x).isSome || (i.bind fun j => ren.lookup j).isSome then
        some (.gen p ((ren.lookup x).getD x) (i.map fun j => (ren.lookup j).getD j) (renameE ren src)) else none
    | _ => none

def isDefer : SExpr → Bool
  | .app _ (.ident _ "$defer") _ _ => true
  | _ => false

/-- Whether evaluating `e` has no effect and reads nothing a `defer:` could
    change (#283): literals, the scope's own constants `vals`, and tuples,
    arrays, maps and options of those. -/
partial def pureVal (vals : List String) : SExpr → Bool
  | .int .. | .float .. | .char .. | .char32 .. => true
  | .str _ ps => ps.all fun | .text _ => true | .code _ => false
  | .ident _ n => vals.contains n || n == "false" || n == "true"
  | .neg _ e => pureVal vals e
  | .tuple _ es | .arrayLit _ es => es.all (pureVal vals)
  | .mapLit _ kvs => kvs.all fun (k, v) => pureVal vals k && pureVal vals v
  | .optionLit _ (.block _ [e]) => pureVal vals e
  | _ => false

/-- A scope's `defer:`s, in order, each with the names its scope declares
    after it renamed (`$later'N`, shown as written): moved after the
    scope's value, they still cannot use those, as where they were (#283,
    #391's review). -/
def deferBodies (ss : List SExpr) : List SExpr :=
  ss.zipIdx.filterMap fun (s, i) =>
    if !isDefer s then none else
    let later := boundIn (ss.drop (i + 1))
    some (if later.isEmpty then s else renameE (renamedFor "$later" later) s)

/-- Whether an exit in `e` can leave it: a `return`, or a `break` outside the
    loops in `e` (marked `$refineBreak` in a branch lifted apart). -/
partial def leaves : SExpr → Bool
  | .ret .. | .brk _ | .app _ (.ident _ "$refineBreak") [] false => true
  | .loop _ body => hasReturn body
  | e => e.children.any leaves

mutual
/-- `e`, a statement or clause of a scope whose `defer:`s `ds` (in order)
    `deferLast` moves after its value, with them pending for the exits in
    it, as a scope's are for every `return` or `break` that leaves it (#283):
    `$deferExits(ds, e)`, which the elaborator registers around `e` as it
    does a `defer:` around the rest of its scope. So they run at each exit
    that leaves `e`, after a `return`'s value and the cleanup of the scopes
    inside `e`, wherever `e` is compiled to. A binding keeps its name, a
    choice its alternatives (each with them), and the `if` of a choice of its
    branches its shape (`deferExitsIf`). -/
partial def deferExits (ds : List SExpr) (e : SExpr) : SExpr :=
  if ds.isEmpty || !leaves e then e else
  match e with
  | .decl p x t v rhs => .decl p x t v (deferExits ds rhs)
  | .gen p x i src => .gen p x i (deferExits ds src)
  | .set p l op rhs => if leaves l then pending e else .set p l op (deferExits ds rhs)
  | .app p f@(.ident _ "$choice") as false => .app p f (as.map (deferExits ds)) false
  | .app p f@(.ident _ "$choiceAt") (l :: as) false => .app p f (l :: as.map (deferExits ds)) false
  | .app p f@(.ident _ "$branchChoice") [i] false => .app p f [deferExitsIf ds i] false
  | .app p f@(.ident _ "$branchChoiceAt") [l, i] false => .app p f [l, deferExitsIf ds i] false
  | e => pending e
where
  pending (e : SExpr) : SExpr := .app e.pos (.ident e.pos "$deferExits") [.block e.pos ds, e] false

/-- The `if` of a choice of its branches with the `defer:`s `ds` pending for
    the exits in it (`deferExits`), its shape kept: in its conditions, a
    scope of their own whose `defer:`s run where they end (`pendingIn`), in
    each branch, and in the `else if`s of its chain. (A `defer:` among
    conditions with a choice of their own is refused, #208: those are left
    as they are, for the elaborator to refuse it.) -/
partial def deferExitsIf (ds : List SExpr) : SExpr → SExpr
  | .ite p cs t u =>
    let (cs, own) := if cs.any liftsHere then (cs.map (deferExits ds), []) else pendingIn ds cs
    .ite p (cs ++ if own.isEmpty then [] else [.block p (own ++ [.int p 0])]) (deferExits ds t)
      (u.map (deferExitsIf ds))
  | e => deferExits ds e

/-- A scope's statements `ss` but its `defer:`s, each with those before it
    pending for its exits, inside the `defer:`s `outer` of the scopes around
    it (`deferExits`); and its `defer:`s in order (`deferBodies`), to run
    where it ends. -/
partial def pendingIn (outer ss : List SExpr) : List SExpr × List SExpr :=
  let ds := deferBodies ss
  ((ss.foldl (fun (out, n) s => if isDefer s then (out, n + 1)
    else (out.push (deferExits outer (deferExits (ds.take n) s)), n)) (#[], 0)).1.toList, ds)
end

/-- `e` without the `defer:`s pending around it (`deferExits`), and how to
    put them back. -/
def underDeferExits : SExpr → SExpr × (SExpr → SExpr)
  | .app q f@(.ident _ "$deferExits") [ds, e] false => (e, fun e' => .app q f [ds, e'] false)
  | e => (e, id)

/-- A scope's own `defer:` blocks after its value, as LANGUAGE.md lowers them
    (#283): its other statements, its value, a block of the `defer:`s in
    order (which runs them where it ends, last registered first, as the
    elaborator checks a `defer:`), then the value again. Once the scope's
    clauses are the caller's, the block runs for each of its values, when
    the value leaves the scope, and not for a value whose clauses fail. The
    value is bound to `dv` first, unless it reads nothing the block could
    change (`pureVal`), so it keeps the type its place gives it (`false`,
    `(Y, array{})`); a scope ending in a `defer:` has the block itself as
    its value, as a block ending in one does. Each statement has the
    `defer:`s before it pending for its exits (`pendingIn`), so a `return`
    or `break` that leaves the scope runs them as well. -/
def deferLast (p : Pos) (dv : String) (ss : List SExpr) : List SExpr :=
  if !ss.any isDefer then ss else
  let (stmts, ds) := pendingIn [] ss
  if ss.getLast?.any isDefer then stmts ++ [.block p ds] else
  match stmts.getLast? with
  | some l =>
    let rest := stmts.dropLast
    let run := SExpr.block p (ds ++ [.int p 0])
    let vals := ss.filterMap fun | .decl _ x _ false _ => some x | _ => none
    if pureVal vals l then rest ++ [run, l] else
    match l with
    -- (a binding as the value stays one, its name then in scope too)
    | .decl q x _ false _ => rest ++ [l, run, .ident q x]
    | .decl q x _ true _ => rest ++ [l, .decl p dv none false (.ident q x), run, .ident p dv]
    | _ => rest ++ [.decl p dv none false l, run, .ident p dv]
  | none => ss

/-- (#283) A block whose clauses are taken apart, with its own `defer:`s after
    its value (`deferLast`, its value's name made from its place): what a
    lazily taken group's code does with a block the lifter would lift, so
    they run as each value leaves it there too. -/
def deferLastBlock : SExpr → SExpr
  | .block p ss => .block p (deferLast p (madeName "dv" "" p) ss)
  | e => e

mutual
/-- An inlined call's parameters bound to its arguments, lifted, in order
    (#235): `pre` is the template's parameter bindings (with `$arg` where
    the argument goes), then (`unpacks`) the bindings that take a tuple
    argument apart. A generic callee's (its template led by `$tparams`) are
    bound together, `$params`, which infers its type arguments from the
    arguments as at a call and names them for the written types after. -/
partial def bindParams (isVal : String → Bool) (isField : String → String → Bool) (p : Pos) (pre : List SExpr)
    (args : List SExpr) (unpacks : Bool := true) : LM Unit := do
  let (frees, pre) := pre.partition fun | .app _ (.ident _ "$freeNames") _ false => true | _ => false
  for fr in frees do
    LM.push fr
  let (marks, pre) := pre.partition fun | .app _ (.ident _ "$tparams") _ false => true | _ => false
  let (pds, unpack) := (pre.take args.length, pre.drop args.length)
  let marked (template value : SExpr) := match template with
    | .decl _ _ _ _ (.app q (.ident _ "$typeValue") [_] false) =>
      SExpr.app q (.ident q "$typeValue") [value] false
    | _ => value
  match marks with
  | .app _ _ tps _ :: _ =>
    -- (each argument evaluated where it is, in order: one that a later
    -- argument's lifted choice would otherwise follow is bound first, to
    -- a name of its own, unless it takes its type from its parameter)
    let fromContext : SExpr → Bool
      | .ident _ "false" | .arrayLit _ [] | .mapLit _ [] => true
      | _ => false
    let mut binds : Array SExpr := #[]
    for ((pd, a), i) in (pds.zip args).zipIdx do
      let a' ← liftE isVal isField a
      let later := (args.drop (i + 1)).any hasLiftable
      let a'' ← if later && !fromContext a' && !stable isVal a' then LM.bind a.pos "t" a' else pure a'
      match pd with
      | .decl q x ty v _ => binds := binds.push (.decl q x ty v (marked pd a''))
      | _ => pure ()
    LM.push (.app p (.ident p "$params") (.block p binds.toList :: tps) false)
  | _ =>
    for (pd, a) in pds.zip args do
      let a' ← liftE isVal isField a
      match pd with
      | .decl q x ty v _ => LM.push (.decl q x ty v (marked pd a'))
      | _ => pure ()
  if unpacks then
    for u in unpack do
      LM.push u

/-- `e` with its liftable choices lifted (into the state's clauses). -/
partial def liftE (isVal : String → Bool) (isField : String → String → Bool) (e : SExpr) : LM SExpr := do
  if !hasLiftable e then return e
  -- A source `first{I := lo..hi; ...}` has a synthesized array producer.
  -- A marked bound cast belongs before that producer, so its refinement
  -- reaches the first's remaining clauses. Keep ordinary ranges on their
  -- existing path, and bind both bounds in their written evaluation order.
  if let some (lo, hi, rebuild) := firstRangeBounds? e then
    let marked := fun x => anyE (fun | .app _ (.ident _ "$liftCast") _ false => true | _ => false) x
    if marked lo || marked hi then
      let bounds ← liftOps isVal isField [lo, hi]
      return ← LM.bind e.pos "c" (rebuild bounds[0]! bounds[1]!)
  match e with
  | .app p (.ident _ "$producerAnchor") [original, lowered] false => do
    let name ← LM.fresh p "producer"
    let metadata := SExpr.decl p name none false original
    LM.push (.app p (.ident p "$producerAnchorStart") [metadata] false)
    let value ← liftE isVal isField lowered
    LM.push (.decl p name none false value)
    LM.push (.app p (.ident p "$producerAnchorEnd") [metadata] false)
    return .ident p name
  | .app p (.ident _ "$choiceProducer") _ false => LM.bind p "c" e
  | .app p (.ident _ "$choice") _ false => LM.bind p "c" e
  | .app p (.ident _ "$liftCast") [c] false => LM.bind p "k" c
  | .set p .. =>
    -- A set used as an operand keeps its result while its existing path
    -- lifter orders indices, RHS, and the write, as for a set clause.
    let result ← LM.fresh p "s"
    liftInto isVal isField (.decl p result none false e)
    return .ident p result
  | .ite p .. =>
    if isBranchy.complete e then
      LM.bind p "c" (.app p (.ident p "$branchChoice") [e] false)
    else
      LM.bind p "c" (.app p (.ident p "$branchChoice") [fillElse e] false) (some (.name "void"))
  | .caseE p x arms =>
    -- (#283) a `case`: its scrutinee first; then, with something to lift in
    -- an arm, the `if` chain that selects it (`caseIf`), a block of its
    -- selector and the `if`, lifted as any block and `if` are
    let e' := SExpr.caseE p (← liftE isVal isField x) arms
    if !arms.any (hasLiftable ·.2) then return e'
    match caseIf (← LM.fresh p "k") e' with
    | some (sel, chain) => liftE isVal isField (.block p [sel, chain])
    | none => return e'
  | .app p (.ident q "$each") [.app p2 g args br] false =>
    -- (a call of a recursive function with several values, #235: the
    -- choices in its arguments lifted, then each argument bound, so that
    -- one that fails is a clause that fails where it is, before the array
    -- of the function's values is computed)
    let args' ← liftOps isVal isField args
    let args'' ← args'.mapM fun a => if stable isVal a then pure a else LM.bind a.pos "t" a
    LM.bind p "c" (.app p (.ident q "$each") [.app p2 g args'' br] false)
  | .app p (.ident _ "$each") _ false => LM.bind p "c" e
  | .app p (.ident q "$loop") (fn :: .block _ pre :: ps :: cls :: tl :: args) false =>
    -- a call of a recursive function with several values taken lazily
    -- (#246): the arguments into its (renamed) parameters, as for
    -- `$inline`, then the call, without them, bound to a name: the
    -- consumer of that binding takes its values one at a time (a call
    -- whose clauses fail has none, and what its arguments did stays, as
    -- for one computed at the call)
    LM.push (.app fn.pos (.ident fn.pos "$fxOf") [fn] false)
    bindParams isVal isField p pre args
    LM.bind p "c" (.app p (.ident q "$loop") [fn, ps, cls, tl] false)
  | .app p (.ident _ "$loop") _ false => LM.bind p "c" e
  -- (#283) a call of a lazily taken group in its own code: its arguments,
  -- then the call bound, as a choice is (`markPoints`)
  | .app p (.ident q "$point") [c] false => LM.bind p "c" (.app p (.ident q "$point") [← liftE isVal isField c] false)
  | .app _ (.ident _ "$deferExits") [.block _ ds, x] false =>
    -- (#283) a scope's `defer:`s pending for the exits in `x`, `deferExits`:
    -- and so for those in each clause lifted out of it
    let saved := (← get).pre
    modify fun s => { s with pre := #[] }
    let x' ← liftE isVal isField x
    modify fun s => { s with pre := saved ++ s.pre.map (deferExits ds) }
    return deferExits ds x'
  | .app _ (.ident _ "$inline") (_ :: .block _ tmpl :: args) false =>
    -- a call of a function with several values (#235): the arguments, in
    -- order, into its (renamed) parameters, then its body's clauses, then
    -- its value's name
    let (marks, tmpl) := tmpl.partition fun
      | .app _ (.ident _ "$tparams") _ false | .app _ (.ident _ "$freeNames") _ false => true
      | _ => false
    let body := tmpl.drop args.length
    -- (the callee's declared effects, which the caller must allow, as at a
    -- call: noted by `$fxOf`, since no call is left)
    if let .app _ _ (fn :: _) _ := e then
      LM.push (.app fn.pos (.ident fn.pos "$fxOf") [fn] false)
    bindParams isVal isField e.pos (marks ++ tmpl.take args.length) args (unpacks := false)
    match body.getLast? with
    | some (.decl q r _ _ _) =>
      let saved := (← get).site
      let inlineSaved := (← get).inlineSite
      modify fun s => { s with site := r, inlineSite := r }
      LM.push (.app q (.ident q "$inlineScope") [.str q [.text r]] false)
      -- (the body's own names are values too: its parameters and locals)
      let bound := boundIn tmpl
      let isVal' := fun n => isVal n || bound.contains n
      for c in body do liftInto isVal' isField c
      modify fun s => { s with site := saved, inlineSite := inlineSaved }
      LM.push (.app q (.ident q "$inlineScopeEnd") [] false)
      return .ident q r
    -- (no template: only seeing whether a body has several values)
    | _ => LM.bind e.pos "c" e
  | .app p f@(.ident _ "$mapKeySources") [keys, value] false =>
    return .app p f [keys, ← liftE isVal isField value] false
  | .app p f args br =>
    let (hs, whole) := headOps isVal isField f
    -- (a call evaluates its positional arguments, then its named ones as
    -- written, then the defaults of those omitted, #283: the arguments are
    -- put in that order, which changes nothing else, and a named one's
    -- value is lifted as an argument is)
    let named := fun | SExpr.decl _ n _ _ _ => n.startsWith "?" | _ => false
    let args := args.filter (!named ·) ++ args.filter named
    let val := fun | a@(SExpr.decl _ n _ _ x) => if n.startsWith "?" then x else a | a => a
    let ops' ← liftOps isVal isField (hs ++ args.map val)
    let hs' := ops'.take hs.length
    let args' := (args.zip (ops'.drop hs.length)).map fun
      | (.decl q n t v _, x) => if n.startsWith "?" then .decl q n t v x else x
      | (_, x) => x
    let f' := match f, hs' with
      | .member q _ m, [o] => if whole then o else .member q o m
      | _, [h] => h
      | _, _ => f
    return .app p f' args' br
  -- (operands evaluated left to right, once each, `liftOps`: those of
  -- arithmetic, member access, `?`, tuples, arrays, maps and string
  -- interpolation; #283, a range's bounds, so a `for`'s range is a
  -- generator after them)
  | .mapLit p entries =>
    -- Prefix bindings can hide a key's failure. Retain its source for a
    -- type-only check at the map's inferred key type, without reexecution.
    let value := e.withChildren (← liftOps isVal isField e.children)
    -- Keys whose own choices were already lifted retain that existing
    -- path; only newly hoisted ordinary keys need this additional check.
    let keys := (entries.map (·.1)).filter (!hasLiftable ·)
    return .app p (.ident p "$mapKeySources") [.block p keys, value] false
  | .bin .. | .range .. | .member .. | .query .. | .neg .. | .tuple .. | .arrayLit .. =>
    return e.withChildren (← liftOps isVal isField e.children)
  -- (#723) a string's interpolated values, as `liftOps` takes operands, but
  -- one before the last with something to lift is bound as its text,
  -- `"{e}"`, not as its value: interpolation calls `ToString` on each value
  -- where it is written, before the code of the next one runs, and
  -- `ToString` of an int beyond 64 bits is the overflow error (#724), which
  -- must stop the program before what the later values' lifted clauses do
  | .str p parts =>
    let codes := parts.filterMap fun | .code c => some c | .text _ => none
    match (codes.zipIdx.filter (hasLiftable ·.1)).getLast?.map (·.2) with
    | none => return e
    | some j =>
      let mut out : Array SPart := #[]
      let mut i := 0
      for part in parts do
        match part with
        | .text _ => out := out.push part
        | .code c =>
          if i < j then
            let c' ← liftE isVal isField c
            -- (a literal's text is its own: nothing to do before the rest)
            let literal := match c' with
              | .int .. | .char .. | .char32 .. | .float .. => true
              | .str _ ps => ps.all fun | .text _ => true | .code _ => false
              | _ => false
            out := out.push (.code (← if literal then pure c' else LM.bind c.pos "t" (.str c.pos [.code c'])))
          else if i == j then out := out.push (.code (← liftE isVal isField c))
          else out := out.push part
          i := i + 1
      return .str p out.toList
  -- (#283) `A and B`: its operands in order, in one block, as the `and` is
  -- a scope of its own whose names `B` sees (Book of Verse ch. 7): `A` a
  -- clause, then `B` the value
  | .andE p a b => liftE isVal isField (.block p [a, b])
  | .orE .. => liftE isVal isField (orIf (← get).site e)
  | .cmp p a rest => liftCmp isVal isField p (a :: rest.map (·.2)) (rest.map (·.1))
  | .construct p n ts fs =>
    -- (#283) a construction's field values, as a call's arguments, in the
    -- order it evaluates them (so they are put in that order first, which
    -- changes nothing else).
    -- Keep unknown layouts and duplicate fields for their normal errors.
    -- Computed defaults before a choice are explicit typed operands; object
    -- allocation, blocks and trailing defaults remain in the construction.
    let info := (← get).fieldOrder n
    let active := (← get).inlineSite
    let site := if active.isEmpty then info.inlineSite else active
    if info.probe then
      return .app p (.ident p "$constructProbe") [.str p [.text site], e] false
    let ord := info.fields
    let names := fs.filterMap fun | .decl _ f none false _ => some f | _ => none
    if ord.isEmpty || names.length != fs.length then
      return noLift p "a construction here, whose fields' order is not known yet" e
    if let some f := names.find? (fun f => (names.filter (· == f)).length > 1) then
      return noLift p s!"a construction that gives field '{f}' twice" e
    let idx := fun (f : String) => (ord.map (·.1)).idxOf f
    -- (#724) When each value runs: the fields given take, in the order
    -- written, the places the given fields have in declaration order (so
    -- `pt{Y := F(), X := G()}` runs `F` first, as on Epic's Verse VM,
    -- differential/struct-archetype-order), and an omitted default keeps its
    -- own place. `at f` is that place, a declaration index.
    let places := (names.map idx).mergeSort (· ≤ ·)
    let at_ := fun (f : String) => match names.idxOf? f with
      | some k => places.getD k (idx f)
      | none => idx f
    let fs := fs.mergeSort fun a b => match a, b with
      | .decl _ f _ _ _, .decl _ g _ _ _ => at_ f ≤ at_ g
      | _, _ => true
    let lastAt := (fs.filterMap fun | .decl _ f _ _ x => if hasLiftable x then some (at_ f) else none | _ => none).foldl max 0
    -- Defaults before the last choice are explicit operands of this
    -- construction. The marker restores their home scope and field type.
    let context : List SExpr := [.str p [.text site], .str p [.text info.origin],
      .app p (.ident p "$constructHints") [.block p info.hints] false, .construct p n ts []]
    let early := (ord.take lastAt).filter fun (f, d) => d && !names.contains f
    let defaults := early.map fun (f, _) =>
      SExpr.decl p f none false (.app p (.ident p "$fieldDefault")
        (context ++ [.ident p f]) false)
    let fs : List SExpr := (fs ++ defaults).mergeSort fun a b => match a, b with
      | .decl _ f _ _ _, .decl _ g _ _ _ => at_ f ≤ at_ g
      | _, _ => true
    let fs : List SExpr := fs.map fun
      | .decl q f t v x =>
        if at_ f < lastAt && !hasLiftable x && !stable isVal x &&
            !(match x with | .app _ (.ident _ "$fieldDefault") _ false => true | _ => false) then
          .decl q f t v (.app q (.ident q "$fieldValue")
            (context ++ [.ident p f, x]) false)
        else .decl q f t v x
      | x => x
    let vals ← liftOps isVal isField (fs.map fun | .decl _ _ _ _ x => x | x => x)
    return .construct p n ts ((fs.zip vals).map fun
      | (.decl q f t v _, x) => .decl q f t v x
      | (_, x) => x)
  | .block p ss =>
    -- (#283) a block with a choice: its clauses into the caller's, as an
    -- inlined body's, its names renamed for this place (so they stay its
    -- own), its last expression the value; its `defer:`s after the value,
    -- `deferLast`, so they run as each value leaves it
    -- (a range bound with no type is a for's generator: in a block it is an
    -- error, which it must stay, so it stays an expression, a range only the
    -- iterated expression of a `for` may be: the Book of Verse's rule)
    let ss := ss.map fun
      | .decl q x none false r@(.range ..) => .decl q x none false (.block r.pos [r])
      | s => s
    let ssD ← if ss.any isDefer then do pure (deferLast p (← LM.fresh p "dv") ss) else pure ss
    let tag ← LM.fresh p "b"
    -- (its names are not in scope where it is, as for a block's own,
    -- `$declNames`: Verse has no shadowing)
    for d in declNames p (localDecls e) do LM.push d
    let ss := stmtsOf (renameE (renamedFor tag (localsOf e)) (.block p ssD))
    let bound := boundIn ss
    let isVal' := fun n => isVal n || bound.contains n
    let (init, last) := (ss.dropLast, ss.getLast?)
    for c in init do liftInto isVal' isField c
    match last with
    | some c@(.decl q x _ _ _) =>
      liftInto isVal' isField c
      return .ident q x
    -- (#283) a `set` with something to lift, as the value: bound to a name
    -- of its own, as `X := (set …)` is
    | some l@(.set q sl _ r) =>
      if !(pathHas hasLiftable sl || hasLiftable r) then liftE isVal' isField l else
      let x ← LM.fresh q "s"
      liftInto isVal' isField (.decl q x none false l)
      return .ident q x
    | some l => liftE isVal' isField l
    | none => return .tuple p []
  | e => return e

/-- A comparison chain `o₀ op₁ o₁ op₂ …` whose operand `oⱼ` is the first with
    a choice: `o₀ … oⱼ₋₁` are bound to names, the pairs among them checked
    (the chain stops at the first that fails, before the choice), then the
    rest of the chain goes on from `oⱼ₋₁`. Its value is `o₀`. -/
partial def liftCmp (isVal : String → Bool) (isField : String → String → Bool) (p : Pos)
    (os : List SExpr) (syms : List String) : LM SExpr := do
  match (os.zipIdx.find? (hasLiftable ·.1)).map (·.2) with
  | none =>
    match os with
    | o :: more => return .cmp p o (syms.zip more)
    | [] => return .tuple p []
  | some 0 =>
    -- (the choice in the first operand: lifted, then the chain from it)
    match os with
    | o :: more =>
      let o' ← liftE isVal isField o
      -- (one kept after all, with a choice still in it: the chain stays as
      -- it is, for the elaborator to refuse)
      if hasLiftable o' then return .cmp p o' (syms.zip more)
      liftCmp isVal isField p (o' :: more) syms
    | [] => return .tuple p []
  | some j =>
    -- (the operands before it, each bound, then the pairs among them)
    let mut hs : Array SExpr := #[]
    for o in os.take j do
      hs := hs.push (← if stable isVal o then pure o else LM.bind o.pos "t" o)
    let h0 := hs[0]!
    if j ≥ 2 then
      LM.push (.cmp p h0 ((syms.take (j - 1)).zip (hs.toList.drop 1)))
    let oj ← liftE isVal isField os[j]!
    let rest := oj :: os.drop (j + 1)
    let r ← if hasLiftable oj then pure (.cmp p hs.back! ((syms.drop (j - 1)).zip rest))
      else liftCmp isVal isField p (hs.back! :: rest) (syms.drop (j - 1))
    if j == 1 then return r
    -- (the rest checked as a clause; the chain's value is its first operand)
    LM.push r
    return h0

/-- Operands evaluated left to right: the liftable choices of each are
    lifted, and every operand before the last one with such a choice is
    bound to a name first (unless `stable`), so it still runs before it. -/
partial def liftOps (isVal : String → Bool) (isField : String → String → Bool) (es : List SExpr) :
    LM (List SExpr) := do
  let last := (es.zipIdx.filter (hasLiftable ·.1)).getLast?.map (·.2)
  match last with
  | none => return es
  | some j =>
    let mut out := #[]
    for (e, i) in es.zipIdx do
      if i < j then
        let e' ← liftE isVal isField e
        -- Names just introduced by this lift are values too. In
        -- particular, a cast's field may be mutable; snapshot its read
        -- before a later operand mutates the object.
        let bound := (← get).pre.toList.flatMap fun
          | .decl _ n _ _ _ => [n]
          | _ => []
        out := out.push (← if stable (fun n => isVal n || bound.contains n) e' then pure e' else LM.bind e.pos "t" e')
      else if i == j then out := out.push (← liftE isVal isField e)
      else out := out.push e
    return out.toList

/-- The clause `c` lifted into the state's clauses, each choice the value of
    a binding (`normClauses`), named for the current site. -/
partial def liftInto (isVal : String → Bool) (isField : String → String → Bool) (c : SExpr) : LM Unit := do
  for c' in normClauses (← liftClauseM isVal isField c) (← get).site do LM.push c'

/-- `liftClause` in the current state (an inlined body's clauses, #235). -/
partial def liftClauseM (isVal : String → Bool) (isField : String → String → Bool) (c : SExpr) :
    LM (List SExpr) := do
  let run (k : LM SExpr) : LM (List SExpr) := do
    let saved := (← get).pre
    modify fun s => { s with pre := #[] }
    let c' ← k
    let pre := (← get).pre
    modify fun s => { s with pre := saved }
    return pre.toList ++ [c']
  -- (clauses made here, each lifted in turn)
  let liftAll (h : List SExpr) : LM (List SExpr) := do
    let mut out : List SExpr := []
    for c in h do out := out ++ (← liftClauseM isVal isField c)
    return out
  let site := (← get).site
  -- (#283) a binding's or a `set`'s `A or B` as its `if`, which is then
  -- lifted as one in that place, with no binding of its own
  let c : SExpr := match c with
    | .decl p x ty v rhs => .decl p x ty v (orIf site rhs)
    | .set p l op rhs => .set p l op (orIf site rhs)
    | c => c
  -- (a `set`'s path's indices bound, as `set` evaluates them before the new
  -- value, `setPrefix`; those clauses lifted
  -- in turn when the indices have a choice or a call with several values
  -- to lift, #283)
  let setPrefixM (q : Pos) (l : SExpr) (op : Option String) : LM (List SExpr × Option String × SExpr) := do
    let (h, o?, l') := setPrefix q l op site
    return (← if pathHas hasLiftable l then liftAll h else pure h, o?, l')
  -- (`set L op= r` with `r`'s code lifted, after `L`'s prefix: `wrap` puts
  -- the `set` in its place)
  let liftSet (q : Pos) (l : SExpr) (op : Option String) (r : SExpr) (wrap : SExpr → SExpr) :
      LM (List SExpr) := do
    let (h, o?, l') ← setPrefixM q l op
    return h ++ (← run do return wrap (.set q l' op (withOld q o? (← liftE isVal isField r))))
  -- (`set L = i` with the `if` lifted whole, #235, #283: after `L`'s
  -- prefix, bound to a name of its own at `L`'s type, then set)
  let setIf (p : Pos) (l i : SExpr) : LM (List SExpr) := do
    let (h, _, l') ← setPrefixM p l none
    let n := madeName "c" site p
    return h ++ [.decl p n none false (.app p (.ident p "$branchChoiceAt") [l', i] false), .set p l' none (.ident p n)]
  -- (#283) a `set` with a choice or a call with several values in its
  -- path's indices: each index bound, lifted, in order, then the new
  -- value's code, as `set` evaluates (before the
  -- cases below, which take the path as it is)
  if let .set p l op rhs := c then
    if pathHas hasLiftable l then
      match alts? rhs with
      | some as =>
        let (h, s) := setClauses p l op as site
        return (← liftAll h) ++ [s]
      | none =>
        if op.isNone && liftsAsIf rhs then return ← setIf p l rhs
        return ← liftSet p l op rhs id
  -- (an `if` with choices in its branches as a binding's value, lifted
  -- whole: at its written type, #235, a `var`'s through a name of its own;
  -- as a `set`'s, at `L`'s. Otherwise it is lifted as any value is, below.)
  match c with
  | .decl p x ty false i@(.ite ..) =>
    if liftsAsIf i then return [.decl p x ty false (.app p (.ident p "$branchChoice") [i] false)]
  | .decl p x ty true i@(.ite ..) =>
    if liftsAsIf i then
      let n := madeName "c" site p
      return [.decl p n ty false (.app p (.ident p "$branchChoice") [i] false), .decl p x ty true (.ident p n)]
  | .set p l none i@(.ite ..) =>
    if liftsAsIf i then return ← setIf p l i
  | _ => pure ()
  match c with
  | .app _ (.ident _ "$choice") _ false => return [c]
  -- (`set L = …` as the last clause of a macro, which names its value)
  | .decl p x ty v (.set q l op r) =>
    if pathHas hasLiftable l then
      -- (#283) a choice or a call with several values in its path's
      -- indices, as for a `set` clause
      match alts? r with
      | some as =>
        let (h, s) := setClauses q l op as site
        return (← liftAll h) ++ [.decl p x ty v s]
      | none => liftSet q l op r (.decl p x ty v ·)
    else
    if isChoice r || !hasLiftable r then return [c] else liftSet q l op r (.decl p x ty v ·)
  | .decl p x ty v rhs =>
    if isChoice rhs || !hasLiftable rhs then return [c] else run do
      return .decl p x ty v (← liftE isVal isField rhs)
  | .set p l op rhs =>
    if isChoice rhs || !hasLiftable rhs then return [c] else liftSet p l op rhs id
  | .gen p x i src =>
    if !hasLiftable src then return [c] else run do return .gen p x i (← liftE isVal isField src)
  | e => if !hasLiftable e then return [c] else run (liftE isVal isField e)
end

/-- A clause with the liftable choices inside it lifted: the clauses before
    it, then it. A binding or `set` whose value is a choice, or a clause that
    is one, stays as it is (`normClauses` makes it a binding). -/
def liftClause (isVal : String → Bool) (isField : String → String → Bool) (c : SExpr)
    (site : String := "") (fieldOrder : String → FieldOrder := fun _ => {}) : List SExpr :=
  (liftClauseM isVal isField c).run' { site, fieldOrder }

/-- (#331) In a `for`, an `if` with choices in its branches as an exclusive
    choice of them (#314): its condition once (a selector, or an option of
    the names it binds for its branch), then the branch it picks, whose own
    choice, if it has one, is the only generator, as for any `if`. An `if`
    picks one branch, once; only the choices the program reaches generate.
    An `else if` is the else branch's own `if`, made one of these in turn. -/
def bifToExcl (c : SExpr) : List SExpr :=
  -- (`set L = if …`'s too, #331: its value bound first, then set, as before,
  -- the branches at `L`'s type when no type is written)
  let (c, place) : SExpr × List SExpr := match c with
    | .decl p x ty false (.app q (.ident q2 "$branchChoiceAt") [l, i] false) =>
      (SExpr.decl p x ty false (.app q (.ident q2 "$branchChoice") [i] false), [l])
    | c => (c, [])
  match c with
  | .decl p x ty false (.app _ (.ident _ "$branchChoice") [i@(.ite ip cs t (some u))] false) =>
    -- (with no type written, its branches' values are at their join, as an
    -- `if`'s: the `if` goes with it, `$joinOf`, for the elaborator to join)
    let withJoin (e : SExpr) : SExpr := match ty, e with
      | none, .app q f as b => .app q f (as ++ [.app ip (.ident ip "$joinOf") (i :: place) false]) b
      | _, e => e
    -- (with the `if`'s place: an `else if`'s binds the same name, in the
    -- path of the one around it)
    -- Generated dispatch cases share a source position and result name;
    -- their distinct condition binders also distinguish these temporaries.
    let names := boundIn cs
    let k := s!"{x}$k{ip.line}_{ip.col}" ++ names.headD ""
    -- (#283) a block as a branch: its names renamed for it, `$…'N`, as the
    -- clauses after the `if` follow it in its path; as written, not in
    -- scope where the `if` is (`$declNames`), as for any block; its
    -- `defer:`s after its value, `deferLast`, so they run as each of its
    -- values leaves it, in a `for`'s path or a choice's alternative
    -- (with the `defer:`s of a scope around the `if` pending for a branch's
    -- exits, `deferExits`, around it)
    let blockNames (b : SExpr) : List SExpr := match (underDeferExits b).1 with
      | b@(.block ..) => declNames ip (localDecls b)
      | _ => []
    let renameBlock (side : String) (b : SExpr) : SExpr :=
      let (b, pending) := underDeferExits b
      pending <| match b with
        | .block .. => match renameE (renamedFor s!"${k}{side}" (localsOf b)) b with
          | .block bp ss => .block bp (deferLast bp s!"${k}{side}$dv" ss)
          | b' => b'
        | b => b
    -- (the names the condition binds, for its branch, `exclOfIf`; renamed
    -- for the branch, `$…'N`, since the clauses after the `if` follow it in
    -- its path, where they are not in scope; as written, not in scope where
    -- the `if` is either: no shadowing)
    let ρ := renamedFor s!"${k}" names
    let written := declNames ip (condDecls ip cs)
    -- (a then-block that binds a name its condition binds: shadowing)
    let shadows := match (underDeferExits t).1 with
      | t@(.block ..) => shadowsIn ip names t
      | _ => []
    let (sel, excl) := exclOfIf ip k (cs.map (renameE ρ)) (renameE ρ (renameBlock "t" t)) (renameBlock "u" u)
    shadows ++ blockNames t ++ blockNames u ++ written ++ [sel, .decl p x ty false (withJoin excl)]
  | c => [c]

/-- Apply a consumer inside each selected branch. Condition names stay in
    the branch, with fresh names so the consumer cannot refer to them. -/
partial def consumeBranches (i : SExpr) (site : String) (consume : SExpr → SExpr) : SExpr :=
  match i with
  | .ite p cs t (some u) =>
    let names := boundIn cs
    let ren := renamedFor s!"${site}{p.line}_{p.col}" names
    let written := declNames p (condDecls p cs)
    let shadows := shadowsIn p names t
    .block p (written ++ shadows ++ [.ite p (cs.map (renameE ren)) (consume (renameE ren t))
      (some (consumeBranches u (site ++ "e") consume))])
  | e => consume e

/-- The clauses ready for compiling: choices inside expressions lifted, and
    each choice the value of a binding. `isVal` says which names are values
    (variables and fields in scope); the clauses' own bindings are too. -/
def prepare (cs : List SExpr) (isVal : String → Bool := fun _ => false)
    (isField : String → String → Bool := fun _ _ => false) (site : String := "")
    (fieldOrder : String → FieldOrder := fun _ => {}) (keepExcl : Bool := false)
    (guardBranches : Bool := true) (keepBranches : SExpr → Bool := fun _ => false) : List SExpr :=
  -- (an exclusive choice is a `for`'s to compile, #314; elsewhere, where
  -- the first success is taken, the choice of its alternatives)
  let cs := if keepExcl then cs else cs.map exclToChoice
  let bound := boundIn cs
  let ps := normClauses (cs.flatMap (liftClause (fun n => isVal n || bound.contains n) isField · site fieldOrder)) site
  -- (in a `for`, an `if` with choices in its branches an exclusive choice of
  -- them, #331; where the first success is taken, one with more in its
  -- branches to lift than the elaborator takes, #283, the choice of those,
  -- each guarded by its branch; not for an `F$all`'s, `gensOf`, whose `if`
  -- gives its branch's array, `arrOfE`)
  if keepExcl then ps.flatMap (fun c =>
    if (binding? c).any (fun b => b.branchy.any keepBranches) then [c] else bifToExcl c)
  else if !guardBranches then ps else ps.flatMap fun c => match c with
    | .decl _ _ _ false (.app _ (.ident _ b) is false) =>
      if (b == "$branchChoice" || b == "$branchChoiceAt") &&
          is.getLast?.any (fun i => !keepBranches i && liftsAsIf i && !plainBranches hasLiftable i) then
        -- (with no type written, the `if` still with it, `$joinOf`, for the
        -- elaborator to type the choice at the branches' join, `elabOneGo`)
        (bifToExcl c).map fun
          | .decl p x ty v e@(.app _ (.ident _ "$excl") as false) =>
            let joins := as.filter isJoinOf
            match exclToChoice e with
            | .app q f cs b => .decl p x ty v (.app q f (cs ++ joins) b)
            | e' => .decl p x ty v e'
          | c => exclToChoice c
      else [c]
    | c => [c]

/-- The lexical inline scope after a prepared suffix. Consumer lowering
    can compile the suffix in a nested block while returning its bound names. -/
def inlineScopesAfter (initial : List String) (cs : List SExpr) : List String :=
  cs.foldl (fun scopes c => match c with
    | .app _ (.ident _ "$inlineScope") [.str _ [.text name]] false => name :: scopes
    | .app _ (.ident _ "$inlineScopeEnd") [] false => scopes.drop 1
    | _ => scopes) initial

/-- Whether the clauses have a choice for their failure context to take. -/
def hasChoice (cs : List SExpr) (fieldOrder : String → FieldOrder := fun _ => {}) : Bool :=
  (prepare cs (fieldOrder := fieldOrder)).any (fun c => (binding? c).isSome) ||
    -- (#283) or something to lift where a clause takes it: an inlined call
    -- with no choice in it, where an overloaded one's overload has one
    -- value, still has its clauses to lift
    cs.any liftsHere

/-- `first{cs}`, the last clause naming its value. -/
def firstOfClauses (p : Pos) (cs : List SExpr) : SExpr :=
  let (cs', v) : List SExpr × SExpr := match cs.getLast? with
    | some (.decl q x _ _ _) => (cs, .ident q x)
    | some e =>
      let q := e.pos
      let x := s!"$f{q.line}_{q.col}"
      (cs.dropLast ++ [.decl q x none false e], .ident q x)
    | none => (cs, .tuple p [])
  .app p (.ident p "$first") [.block p (cs' ++ [v])] false

/-- With a choice to take, `e` as the first success of it (#208): how
    `option{…}` and `logic{…}` (whose braces hold clauses), `not` and the left
    of `or` take a choice's values. -/
def takeFirst? (e : SExpr) (fieldOrder : String → FieldOrder := fun _ => {}) : Option SExpr :=
  match e with
  | .block p cs => if hasChoice cs fieldOrder then some (firstOfClauses p cs) else none
  -- (#283) a `set` with a choice or a call with several values in its path
  -- or value, as `not (set A[1 | 2] = 5)`: its value bound to a name, as a
  -- block's last `set` is (`hasLiftable` sees a `set` only as a clause)
  | e@(.set _ l _ r) => if hasLiftable r || pathHas hasLiftable l then some (firstOfClauses e.pos [e]) else none
  | e => if hasLiftable e then some (firstOfClauses e.pos [e]) else none

end OpenVerse.Front.Choice
