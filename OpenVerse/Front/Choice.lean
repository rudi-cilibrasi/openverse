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
    (none for the last `else`) and its expression. -/
partial def arms : SExpr → List (Option (List SExpr) × SExpr)
  | .ite _ cs t (some e) => (some cs, t) :: arms e
  | e => [(none, e)]

/-- The part of a made name that names an inlined call's site (#235), set
    apart from the position after it (site 1 at line 12 is not site 11 at
    line 2); nothing outside one. -/
def sitePart (site : String) : String := if site.isEmpty then "" else site ++ "@"

/-- The indices of a `set` path bound to names, in order (unless literals),
    and the path with those names in their places: `set` evaluates them
    before the new value. -/
partial def hoistPath (q : Pos) (l : SExpr) (site : String := "") : List SExpr × SExpr :=
  let nm (n : Nat) : String := s!"$i{sitePart site}{q.line}_{q.col}_{n}"
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
    operands): `L`'s indices, then for `op=` its old value, then that code,
    as `set` evaluates. `$withOld(O, R)` tells the elaborator that the old
    value is already in `O`. The result: the clauses before, the old value's
    name, and the path. -/
def setPrefix (q : Pos) (l : SExpr) (op : Option String) (site : String := "") :
    List SExpr × Option String × SExpr :=
  let (h, l') := hoistPath q l site
  match op with
  | none => (h, none, l')
  | some _ =>
    let o := s!"$o{sitePart site}{q.line}_{q.col}"
    (h ++ [.decl q o none false l'], some o, l')

/-- The new value of a `set` whose old one is in `o?`. -/
def withOld (q : Pos) (o? : Option String) (r : SExpr) : SExpr :=
  match o? with
  | some o => .app q (.ident q "$withOld") [.ident q o, r] false
  | none => r

/-- `set L op= a | b` with the choice bound first, as `set` evaluates (Book
    of Verse §3.5): the indices of `L`'s path, then for `op=` the old value,
    then the choice. For `=`, the alternatives take `L`'s type. -/
def setClauses (p : Pos) (l : SExpr) (op : Option String) (as : List SExpr) (q : Pos) (site : String := "") :
    List SExpr × SExpr :=
  let (h, o?, l') := setPrefix q l op site
  let c := s!"$c{sitePart site}{q.line}_{q.col}"
  let choice : SExpr := match op with
    | none => .app q (.ident q "$choiceAt") (l' :: as) false
    | some _ => .app q (.ident q "$choice") as false
  (h ++ [.decl q c none false choice], .set p l' op (withOld q o? (.ident q c)))

/-- The clauses, with each choice the value of a binding: a clause that is a
    choice gets a name of its own, and `set L = a | b` and `var X:t = a | b`
    bind the choice first. -/
def normClauses (cs : List SExpr) (site : String := "") : List SExpr :=
  cs.flatMap fun c =>
    let nm (p : Pos) : String := s!"$c{sitePart site}{p.line}_{p.col}"
    match c with
    | .app p (.ident _ "$choice") _ false => [.decl p (nm p) none false c]
    | .set p l op rhs => match alts? rhs with
      | some as => let (h, s) := setClauses p l op as p site; h ++ [s]
      | none => [c]
    | .decl p x ty true rhs =>
      if isChoice rhs then [.decl p (nm p) ty false rhs, .decl p x ty true (.ident p (nm p))] else [c]
    -- (`set L = a | b` as the last clause of a macro, which names its value)
    | .decl p x ty false (.set q l op rhs) => match alts? rhs with
      | some as => let (h, s) := setClauses q l op as q site; h ++ [.decl p x ty false s]
      | none => [c]
    | c => [c]

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
block's clauses; a construction's fields, in its type's declaration order,
as they are evaluated (#283). A choice elsewhere (a branch that is more
than a value, an alternative, which the elaborator takes apart) is not
lifted here. -/

/-- The variable a `set` path starts from. -/
partial def rootName? : SExpr → Option String
  | .ident _ n => some n
  | .member _ e _ | .app _ e _ true | .query _ e => rootName? e
  | _ => none

/-- The names that `set` writes inside `e`. -/
partial def setsIn : SExpr → List String
  | .set _ l _ r => ((rootName? l).map ([·])).getD [] ++ setsIn l ++ setsIn r
  | .app _ f as _ => setsIn f ++ as.flatMap setsIn
  | .member _ e _ | .query _ e | .neg _ e | .notE _ e | .optionLit _ e | .logicLit _ e | .loop _ e => setsIn e
  | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b => setsIn a ++ setsIn b
  | .cmp _ a rest => setsIn a ++ rest.flatMap (setsIn ·.2)
  | .tuple _ es | .block _ es | .arrayLit _ es => es.flatMap setsIn
  | .ite _ cs t e => cs.flatMap setsIn ++ setsIn t ++ ((e.map setsIn).getD [])
  | .forE _ cs b => cs.flatMap setsIn ++ setsIn b
  | .gen _ _ _ s => setsIn s
  | .ret _ e => (e.map setsIn).getD []
  | .caseE _ s arms => setsIn s ++ arms.flatMap fun (p, v) => ((p.map setsIn).getD []) ++ setsIn v
  | .decl _ _ _ _ e => setsIn e
  | .construct _ _ _ fs => fs.flatMap setsIn
  | .mapLit _ kvs => kvs.flatMap fun (k, v) => setsIn k ++ setsIn v
  | .str _ ps => ps.flatMap fun | .code c => setsIn c | .text _ => []
  | _ => []

/-- The names a clause list binds (so values, for `stable` and the heads
    of calls). -/
def boundIn (cs : List SExpr) : List String :=
  cs.flatMap fun
    | .decl _ x _ _ _ => [x]
    | .gen _ x i _ => x :: i.toList
    | _ => []

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

/-- Whether `e` has a choice that lifting reaches. -/
partial def hasLiftable : SExpr → Bool
  -- (a block or construction kept, with why, `$noLift`, #283)
  | .app _ (.ident _ "$noLift") _ false => false
  -- (an inlined function's parameter default, in its own context, #283)
  | .app _ (.ident _ "$paramDefault") _ false => false
  | .app _ (.ident _ "$choice") _ false => true
  | .app _ (.ident _ "$inline") _ false => true
  | .app _ (.ident _ "$each") _ false => true
  | .app _ (.ident _ "$loop") _ false => true
  | e@(.ite ..) => isBranchy e
  | .app _ f args _ => headHas hasLiftable f || args.any fun
      -- (a named argument's value, #283)
      | .decl _ n _ _ x => n.startsWith "?" && hasLiftable x
      -- (the body of `first{…}`, `spawn`, `branch`, `defer`, `sync`, … is
      -- no value to lift from: its choices are its own)
      | a@(.block ..) => !(match f with | .ident _ n => n.startsWith "$" | _ => false) && hasLiftable a
      | a => hasLiftable a
  | .bin _ _ a b => hasLiftable a || hasLiftable b
  | .cmp _ a rest => hasLiftable a || rest.any (hasLiftable ·.2)
  | .member _ e _ | .query _ e | .neg _ e => hasLiftable e
  | .tuple _ es | .arrayLit _ es => es.any hasLiftable
  | .str _ ps => ps.any fun | .code c => hasLiftable c | .text _ => false
  | .mapLit _ kvs => kvs.any fun (k, v) => hasLiftable k || hasLiftable v
  -- (a construction's field values and a block's clauses, #283)
  | .construct _ _ _ fs => fs.any fun | .decl _ _ _ _ x => hasLiftable x | x => hasLiftable x
  | .block _ ss => ss.any fun
      | .decl _ _ _ _ x | .set _ _ _ x | .gen _ _ _ x => hasLiftable x
      | x => hasLiftable x
  | _ => false

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

structure LiftSt where
  next : Nat := 0
  /-- The clauses lifted so far, in order. -/
  pre : Array SExpr := #[]
  /-- Part of every name made: the call site of the function being inlined
      (#235), so two calls of one function do not make the same names. -/
  site : String := ""
  /-- A struct's or class's fields in declaration order, the order its
      constructions evaluate them in, each with whether it has a default
      that is more than a literal (so runs where it is, #283); `[]` when not
      known here. -/
  fieldOrder : String → List (String × Bool) := fun _ => []

abbrev LM := StateM LiftSt

def LM.fresh (p : Pos) (k : String) : LM String :=
  modifyGet fun s => (s!"${k}{sitePart s.site}{p.line}_{p.col}_{s.next}", { s with next := s.next + 1 })

def LM.bind (p : Pos) (k : String) (e : SExpr) : LM SExpr := do
  let x ← LM.fresh p k
  modify fun s => { s with pre := s.pre.push (.decl p x none false e) }
  return .ident p x

/-- `e` with `f` applied top-down: where `f` gives a replacement, it is used
    (and not descended into). Struct constructions' field names are kept. -/
partial def mapE (f : SExpr → Option SExpr) (e : SExpr) : SExpr :=
  match f e with
  | some e' => e'
  | none =>
    let go := mapE f
    match e with
    | .str p ps => .str p (ps.map fun | .code c => .code (go c) | t => t)
    | .app p g as b => .app p (go g) (as.map go) b
    | .member p x m => .member p (go x) m
    | .query p x => .query p (go x)
    | .neg p x => .neg p (go x)
    | .notE p x => .notE p (go x)
    | .bin p o a b => .bin p o (go a) (go b)
    | .cmp p a r => .cmp p (go a) (r.map fun (o, b) => (o, go b))
    | .andE p a b => .andE p (go a) (go b)
    | .orE p a b => .orE p (go a) (go b)
    | .range p a b => .range p (go a) (go b)
    | .tuple p es => .tuple p (es.map go)
    | .block p es => .block p (es.map go)
    | .arrayLit p es => .arrayLit p (es.map go)
    | .optionLit p x => .optionLit p (go x)
    | .logicLit p x => .logicLit p (go x)
    | .ite p cs t e' => .ite p (cs.map go) (go t) (e'.map go)
    | .forE p cs b => .forE p (cs.map go) (go b)
    | .gen p x i src => .gen p x i (go src)
    | .loop p b => .loop p (go b)
    | .ret p x => .ret p (x.map go)
    | .caseE p sc arms => .caseE p (go sc) (arms.map fun (pt, v) => (pt.map go, go v))
    | .decl p n t v x => .decl p n t v (go x)
    | .set p l o r => .set p (go l) o (go r)
    | .construct p n ts fs => .construct p n ts (fs.map fun
        | .decl q fn t v x => .decl q fn t v (go x)
        | a => go a)
    | .mapLit p kvs => .mapLit p (kvs.map fun (k, v) => (go k, go v))
    | .structDef p tps fs => .structDef p tps (fs.map fun (n, t, d, v) => (n, t, d.map go, v))
    | e => e

/-- Whether some subexpression satisfies `pr` (through `mapE`). -/
partial def anyE (pr : SExpr → Bool) (e : SExpr) : Bool :=
  pr e || match e with
    | .str _ ps => ps.any fun | .code c => anyE pr c | _ => false
    | .app _ g as _ => anyE pr g || as.any (anyE pr)
    | .member _ x _ | .query _ x | .neg _ x | .notE _ x | .optionLit _ x | .logicLit _ x | .loop _ x
    | .gen _ _ _ x | .decl _ _ _ _ x => anyE pr x
    | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b | .set _ a _ b => anyE pr a || anyE pr b
    | .cmp _ a r => anyE pr a || r.any (anyE pr ·.2)
    | .tuple _ es | .block _ es | .arrayLit _ es | .construct _ _ _ es => es.any (anyE pr)
    | .ite _ cs t e' => cs.any (anyE pr) || anyE pr t || (e'.map (anyE pr)).getD false
    | .forE _ cs b => cs.any (anyE pr) || anyE pr b
    | .ret _ x => (x.map (anyE pr)).getD false
    | .caseE _ sc arms => anyE pr sc || arms.any fun (pt, v) => ((pt.map (anyE pr)).getD false) || anyE pr v
    | .mapLit _ kvs => kvs.any fun (k, v) => anyE pr k || anyE pr v
    | _ => false

/-- The statements of a body. -/
def stmtsOf : SExpr → List SExpr
  | .block _ ss => ss
  | e => [e]

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
partial def localDecls (e : SExpr) : List (String × Pos) :=
  let rec go : SExpr → List (String × Pos)
    | .decl p n _ _ x => (if n.startsWith "?" then [] else [(n, p)]) ++ go x
    | .gen p x i src => (x :: i.toList).map (·, p) ++ go src
    | .construct _ _ _ fs => fs.flatMap fun | .decl _ _ _ _ x => go x | a => go a
    | .str _ ps => ps.flatMap fun | .code c => go c | _ => []
    | .app _ g as _ => go g ++ as.flatMap go
    | .member _ x _ | .query _ x | .neg _ x | .notE _ x | .optionLit _ x | .logicLit _ x | .loop _ x => go x
    | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b | .set _ a _ b => go a ++ go b
    | .cmp _ a r => go a ++ r.flatMap (go ·.2)
    | .tuple _ es | .block _ es | .arrayLit _ es => es.flatMap go
    | .ite _ cs t e' => cs.flatMap go ++ go t ++ ((e'.map go).getD [])
    | .forE _ cs b => cs.flatMap go ++ go b
    | .ret _ x => (x.map go).getD []
    | .caseE _ sc arms => go sc ++ arms.flatMap fun (pt, v) => ((pt.map go).getD []) ++ go v
    | .mapLit _ kvs => kvs.flatMap fun (k, v) => go k ++ go v
    | _ => []
  go e

/-- The names `e` binds, at any depth. -/
partial def localsOf (e : SExpr) : List String :=
  ((localDecls e).map (·.1)).eraseDups

/-- `e` with the names in `ren` renamed, binders and uses. -/
partial def renameE (ren : List (String × String)) : SExpr → SExpr :=
  mapE fun
    | .ident p n => (ren.lookup n).map (.ident p ·)
    | .decl p n t v x => (ren.lookup n).map fun n' => .decl p n' t v (renameE ren x)
    | .gen p x i src => if (ren.lookup x).isSome || (i.bind fun j => ren.lookup j).isSome then
        some (.gen p ((ren.lookup x).getD x) (i.map fun j => (ren.lookup j).getD j) (renameE ren src)) else none
    | _ => none

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
    modify fun s => { s with pre := s.pre.push fr }
  let (marks, pre) := pre.partition fun | .app _ (.ident _ "$tparams") _ false => true | _ => false
  let (pds, unpack) := (pre.take args.length, pre.drop args.length)
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
      | .decl q x ty v _ => binds := binds.push (.decl q x ty v a'')
      | _ => pure ()
    modify fun s => { s with pre := s.pre.push (.app p (.ident p "$params") (.block p binds.toList :: tps) false) }
  | _ =>
    for (pd, a) in pds.zip args do
      let a' ← liftE isVal isField a
      match pd with
      | .decl q x ty v _ => modify fun s => { s with pre := s.pre.push (.decl q x ty v a') }
      | _ => pure ()
  if unpacks then
    for u in unpack do
      modify fun s => { s with pre := s.pre.push u }

/-- `e` with its liftable choices lifted (into the state's clauses). -/
partial def liftE (isVal : String → Bool) (isField : String → String → Bool) (e : SExpr) : LM SExpr := do
  if !hasLiftable e then return e
  match e with
  | .app p (.ident _ "$choice") _ false => LM.bind p "c" e
  | .ite p .. => LM.bind p "c" (.app p (.ident p "$branchChoice") [e] false)
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
    modify fun s => { s with pre := s.pre.push (.app fn.pos (.ident fn.pos "$fxOf") [fn] false) }
    bindParams isVal isField p pre args
    LM.bind p "c" (.app p (.ident q "$loop") [fn, ps, cls, tl] false)
  | .app p (.ident _ "$loop") _ false => LM.bind p "c" e
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
      modify fun s => { s with pre := s.pre.push (.app fn.pos (.ident fn.pos "$fxOf") [fn] false) }
    bindParams isVal isField e.pos (marks ++ tmpl.take args.length) args (unpacks := false)
    match body.getLast? with
    | some (.decl q r _ _ _) =>
      let saved := (← get).site
      modify fun s => { s with site := r }
      -- (the body's own names are values too: its parameters and locals)
      let bound := boundIn tmpl
      let isVal' := fun n => isVal n || bound.contains n
      for c in body do
        for c' in normClauses (← liftClauseM isVal' isField c) r do
          modify fun s => { s with pre := s.pre.push c' }
      modify fun s => { s with site := saved }
      return .ident q r
    -- (no template: only seeing whether a body has several values)
    | _ => LM.bind e.pos "c" e
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
  | .bin p o a b => match ← liftOps isVal isField [a, b] with
    | [a', b'] => return .bin p o a' b'
    | _ => return e
  | .cmp p a rest => liftCmp isVal isField p (a :: rest.map (·.2)) (rest.map (·.1))
  | .member p x m => return .member p (← liftE isVal isField x) m
  | .query p x => return .query p (← liftE isVal isField x)
  | .neg p x => return .neg p (← liftE isVal isField x)
  | .tuple p es => return .tuple p (← liftOps isVal isField es)
  | .arrayLit p es => return .arrayLit p (← liftOps isVal isField es)
  | .str p ps =>
    let codes := ps.filterMap fun | .code c => some c | .text _ => none
    let codes' ← liftOps isVal isField codes
    let rec put : List SPart → List SExpr → List SPart
      | .code _ :: ps, c :: cs => .code c :: put ps cs
      | p :: ps, cs => p :: put ps cs
      | [], _ => []
    return .str p (put ps codes')
  | .mapLit p kvs =>
    let flat ← liftOps isVal isField (kvs.flatMap fun (k, v) => [k, v])
    let rec pairs : List SExpr → List (SExpr × SExpr)
      | k :: v :: r => (k, v) :: pairs r
      | _ => []
    return .mapLit p (pairs flat)
  | .construct p n ts fs =>
    -- (#283) a construction's field values, as a call's arguments, in the
    -- order it evaluates them: its type's declaration order, not as written
    -- (so they are put in that order first, which changes nothing else).
    -- Kept (so refused) when that order is unknown here, a field is given
    -- twice (only the first is evaluated), or a field not given whose
    -- default is more than a literal comes before the last choice (it would
    -- run after it)
    let ord := (← get).fieldOrder n
    let names := fs.filterMap fun | .decl _ f none false _ => some f | _ => none
    if ord.isEmpty || names.length != fs.length then
      return noLift p "a construction here, whose fields' order is not known (in a recursive function computed eagerly)" e
    if let some f := names.find? (fun f => (names.filter (· == f)).length > 1) then
      return noLift p s!"a construction that gives field '{f}' twice" e
    let idx := fun (f : String) => (ord.map (·.1)).idxOf f
    let fs := fs.mergeSort fun a b => match a, b with
      | .decl _ f _ _ _, .decl _ g _ _ _ => idx f ≤ idx g
      | _, _ => true
    let lastAt := (fs.filterMap fun | .decl _ f _ _ x => if hasLiftable x then some (idx f) else none | _ => none).foldl max 0
    if let some (f, _) := (ord.take lastAt).find? (fun (f, d) => d && !names.contains f) then
      return noLift p s!"a construction of {n} that does not give field '{f}': its default comes before the choice, and would run after it" e
    let vals ← liftOps isVal isField (fs.map fun | .decl _ _ _ _ x => x | x => x)
    return .construct p n ts ((fs.zip vals).map fun
      | (.decl q f t v _, x) => .decl q f t v x
      | (_, x) => x)
  | .block p ss =>
    -- (#283) a block with a choice: its clauses into the caller's, as an
    -- inlined body's, its names renamed for this place (so they stay its
    -- own), its last expression the value; not with a defer:, whose scope
    -- would change
    if ss.any (fun | .app _ (.ident _ "$defer") _ _ => true | _ => false) then
      return noLift p "a block with a defer: of its own, whose scope would change" e
    -- (a range bound with no type is a for's generator: in a block it is an
    -- error, which it must stay)
    if ss.any (fun | .decl _ _ none false (.range ..) | .gen .. => true | _ => false) then
      return noLift p "a block that binds a range (a..b), which only a for clause can" e
    let tag ← LM.fresh p "b"
    -- (its names are not in scope where it is, as for a block's own,
    -- `$declNames`: Verse has no shadowing)
    let decls := localDecls e
    if !decls.isEmpty then
      modify fun s => { s with pre := s.pre.push (.app p (.ident p "$declNames") (decls.map fun (n, q) => .ident q n) false) }
    -- (`'` sets the name written apart, `shownName`)
    let ren := (localsOf e).map fun n => (n, s!"{tag}'{n}")
    let ss := stmtsOf (renameE ren e)
    let bound := boundIn ss
    let isVal' := fun n => isVal n || bound.contains n
    let site := (← get).site
    let (init, last) := (ss.dropLast, ss.getLast?)
    for c in init do
      for c' in normClauses (← liftClauseM isVal' isField c) site do
        modify fun s => { s with pre := s.pre.push c' }
    match last with
    | some c@(.decl q x _ _ _) =>
      for c' in normClauses (← liftClauseM isVal' isField c) site do
        modify fun s => { s with pre := s.pre.push c' }
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
      modify fun s => { s with pre := s.pre.push (.cmp p h0 ((syms.take (j - 1)).zip (hs.toList.drop 1))) }
    let oj ← liftE isVal isField os[j]!
    let rest := oj :: os.drop (j + 1)
    let r ← if hasLiftable oj then pure (.cmp p hs.back! ((syms.drop (j - 1)).zip rest))
      else liftCmp isVal isField p (hs.back! :: rest) (syms.drop (j - 1))
    if j == 1 then return r
    -- (the rest checked as a clause; the chain's value is its first operand)
    modify fun s => { s with pre := s.pre.push r }
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
        out := out.push (← if stable isVal e' then pure e' else LM.bind e.pos "t" e')
      else if i == j then out := out.push (← liftE isVal isField e)
      else out := out.push e
    return out.toList

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
  let site := (← get).site
  match c with
  | .app _ (.ident _ "$choice") _ false => return [c]
  -- (an `if` with choices in its branches as a binding's value: at its
  -- written type, #235)
  | .decl p x ty false rhs@(.ite ..) =>
    if isBranchy rhs then return [.decl p x ty false (.app p (.ident p "$branchChoice") [rhs] false)] else
      if !hasLiftable rhs then return [c] else run do return .decl p x ty false (← liftE isVal isField rhs)
  | .decl p x ty true rhs@(.ite ..) =>
    if isBranchy rhs then
      let n := s!"$c{sitePart site}{p.line}_{p.col}"
      return [.decl p n ty false (.app p (.ident p "$branchChoice") [rhs] false), .decl p x ty true (.ident p n)]
    else if !hasLiftable rhs then return [c] else run do return .decl p x ty true (← liftE isVal isField rhs)
  | .set p l none rhs@(.ite ..) =>
    if isBranchy rhs then
      let (h, _, l') := setPrefix p l none site
      let n := s!"$c{sitePart site}{p.line}_{p.col}"
      return h ++ [.decl p n none false (.app p (.ident p "$branchChoiceAt") [l', rhs] false), .set p l' none (.ident p n)]
    else if !hasLiftable rhs then return [c] else
      let (h, o?, l') := setPrefix p l none site
      return h ++ (← run do return .set p l' none (withOld p o? (← liftE isVal isField rhs)))
  -- (`set L = …` as the last clause of a macro, which names its value)
  | .decl p x ty v (.set q l op r) =>
    if isChoice r || !hasLiftable r then return [c] else
      let (h, o?, l') := setPrefix q l op site
      return h ++ (← run do return .decl p x ty v (.set q l' op (withOld q o? (← liftE isVal isField r))))
  | .decl p x ty v rhs =>
    if isChoice rhs || !hasLiftable rhs then return [c] else run do
      return .decl p x ty v (← liftE isVal isField rhs)
  | .set p l op rhs =>
    if isChoice rhs || !hasLiftable rhs then return [c] else
      -- (the path's indices, then for `op=` the old value, then the
      -- lifted code, as `set` evaluates)
      let (h, o?, l') := setPrefix p l op site
      return h ++ (← run do return .set p l' op (withOld p o? (← liftE isVal isField rhs)))
  | .gen p x i src =>
    if !hasLiftable src then return [c] else run do return .gen p x i (← liftE isVal isField src)
  | e => if !hasLiftable e then return [c] else run (liftE isVal isField e)
end

/-- A clause with the liftable choices inside it lifted: the clauses before
    it, then it. A binding or `set` whose value is a choice, or a clause that
    is one, stays as it is (`normClauses` makes it a binding). -/
def liftClause (isVal : String → Bool) (isField : String → String → Bool) (c : SExpr)
    (site : String := "") (fieldOrder : String → List (String × Bool) := fun _ => []) : List SExpr :=
  (liftClauseM isVal isField c).run' { site, fieldOrder }

/-- The clauses ready for compiling: choices inside expressions lifted, and
    each choice the value of a binding. `isVal` says which names are values
    (variables and fields in scope); the clauses' own bindings are too. -/
def prepare (cs : List SExpr) (isVal : String → Bool := fun _ => false)
    (isField : String → String → Bool := fun _ _ => false) (site : String := "")
    (fieldOrder : String → List (String × Bool) := fun _ => []) : List SExpr :=
  let bound := boundIn cs
  normClauses (cs.flatMap (liftClause (fun n => isVal n || bound.contains n) isField · site fieldOrder)) site

/-- Whether the clauses have a choice for their failure context to take. -/
def hasChoice (cs : List SExpr) (fieldOrder : String → List (String × Bool) := fun _ => []) : Bool :=
  (prepare cs (fieldOrder := fieldOrder)).any fun c => (binding? c).isSome

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
def takeFirst? (e : SExpr) (fieldOrder : String → List (String × Bool) := fun _ => []) : Option SExpr :=
  match e with
  | .block p cs => if hasChoice cs fieldOrder then some (firstOfClauses p cs) else none
  | e => if hasLiftable e then some (firstOfClauses e.pos [e]) else none

/-! ### Functions with several values (#235)

A top-level function whose body has a choice that no failure context in
it takes (`Digit():int = 0 | 1 | … | 9`) has several values. A call of one
is a choice point: `inlineMulti` drops the function and turns each call into
`$inline(F, template, args…)`, whose template is the body with its
parameters and locals renamed for that call; lifting (`liftE`) puts the
arguments into the parameters, then the body's clauses, into the caller's
clauses, so the body's choices become the caller's. Recursive and generic
ones, ones with named parameters or `return`, and their use as values are
refused for now. -/

/-- A function of the program, by name: its parameters, type parameters,
    effects, result type and body. -/
structure MFn where
  pos : Pos
  params : List SParam
  tparams : List TParam
  fx : List String
  ret : STy
  body : SExpr

/-- The names `e` uses: as identifiers and as calls' heads. -/
partial def namesUsed (e : SExpr) : List String :=
  let rec go : SExpr → List String
    | .ident _ n => [n]
    | .decl _ _ _ _ x => go x
    | .gen _ _ _ src => go src
    | .construct _ _ _ fs => fs.flatMap fun | .decl _ _ _ _ x => go x | a => go a
    | .str _ ps => ps.flatMap fun | .code c => go c | _ => []
    | .app _ g as _ => go g ++ as.flatMap go
    | .member _ x _ | .query _ x | .neg _ x | .notE _ x | .optionLit _ x | .logicLit _ x | .loop _ x => go x
    | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b | .set _ a _ b => go a ++ go b
    | .cmp _ a r => go a ++ r.flatMap (go ·.2)
    | .tuple _ es | .block _ es | .arrayLit _ es => es.flatMap go
    | .ite _ cs t e' => cs.flatMap go ++ go t ++ ((e'.map go).getD [])
    | .forE _ cs b => cs.flatMap go ++ go b
    | .ret _ x => (x.map go).getD []
    | .caseE _ sc arms => go sc ++ arms.flatMap fun (pt, v) => ((pt.map go).getD []) ++ go v
    | .mapLit _ kvs => kvs.flatMap fun (k, v) => go k ++ go v
    | .structDef _ _ fs => fs.flatMap fun (_, _, d, _) => (d.map go).getD []
    | _ => []
  (go e).eraseDups

/-- `e` with every choice `a₁ | … | aₙ` made `if (false?) then a₁ else …
    aₙ`: the body a function with several values keeps, elaborated (so
    type- and effect-checked like any function's) but never called, as its
    calls are inlined. -/
partial def checkBody : SExpr → SExpr :=
  mapE fun
    | .app p (.ident _ "$choice") as false =>
      let rec chain : List SExpr → SExpr
        | [] => .tuple p []
        | [a] => checkBody a
        | a :: rest => .ite p [.query p (.ident p "false")] (checkBody a) (some (chain rest))
      some (chain as)
    | _ => none

/-- A statement where a choice or a call of a function of `mv` (marked) is
    lifted into the body's own clauses: the body then has several values. -/
def liftsHere (c : SExpr) : Bool :=
  match c with
  | .decl _ _ _ _ rhs => hasLiftable rhs
  | .set _ _ _ rhs => hasLiftable rhs
  | .gen _ _ _ src => hasLiftable src
  | e => hasLiftable e

/-- Whether a written type mentions one of the names `tps`. -/
partial def styMentions (tps : List String) : STy → Bool
  | .name n => tps.contains n
  | .arr t | .opt t => styMentions tps t
  | .tup ts => ts.any (styMentions tps)
  | .map k v => styMentions tps k || styMentions tps v
  | .app n ts => tps.contains n || ts.any (styMentions tps)
  | .fn ps _ r => ps.any (styMentions tps) || styMentions tps r

/-- Whether the body writes a type that mentions one of `tps`: in a
    binding's type or a construction's type arguments. -/
partial def writesTypes (tps : List String) (e : SExpr) : Bool :=
  anyE (fun
    | .decl _ _ (some t) _ _ => styMentions tps t
    | .construct _ n ts _ => tps.contains n || ts.any (styMentions tps)
    | _ => false) e

/-- A written type with the names of `ρ` renamed. -/
partial def styRename (ρ : List (String × String)) : STy → STy
  | .name n => .name ((ρ.lookup n).getD n)
  | .arr t => .arr (styRename ρ t)
  | .opt t => .opt (styRename ρ t)
  | .tup ts => .tup (ts.map (styRename ρ))
  | .map k v => .map (styRename ρ k) (styRename ρ v)
  | .app n ts => .app ((ρ.lookup n).getD n) (ts.map (styRename ρ))
  | .fn ps es r => .fn (ps.map (styRename ρ)) es (styRename ρ r)

/-- The types a body writes (bindings', constructions' type arguments) with
    the names of `ρ` renamed: a generic function's type parameters, renamed
    for the site its body is inlined at (#235). -/
partial def renameTypes (ρ : List (String × String)) : SExpr → SExpr :=
  mapE fun
    | .decl p n (some t) v x => some (.decl p n (some (styRename ρ t)) v (renameTypes ρ x))
    | .construct p n ts fs => some (.construct p ((ρ.lookup n).getD n) (ts.map (styRename ρ)) (fs.map (renameTypes ρ)))
    | _ => none

/-- The shape of a recursive function with several values that its
    consumers take lazily (#246), from its body: its clauses, which have no
    choice and call no function with several values, then its last
    expression (or the value of its last binding), a choice or an
    `if … else …` whose branches are choices or values, each alternative a
    whole call of the function itself (`g`) or a value with no choice in
    it. -/
def loopShape? (g : String) (mv : List String) (body : SExpr) : Option (List SExpr × SExpr) := do
  let ss := stmtsOf body
  let last ← ss.getLast?
  let cls := ss.dropLast
  let tail := match last with
    | .decl _ _ _ false rhs => rhs
    | e => e
  -- (no choice, and no call of a function with several values, nor any
  -- other mention of `g`: a call of it its own `if` or `for` takes, say)
  let plain (e : SExpr) : Bool := !liftsHere (markCalls mv e) && !(namesUsed e).contains g
  let isRec : SExpr → Bool
    | .app _ (.ident _ h) as _ => h == g && as.all fun a =>
        plain a && (match a with | .decl .. => false | _ => true)
    | _ => false
  let groupOK (e : SExpr) : Bool := ((alts? e).getD [e]).all fun a => isRec a || plain a
  let tailOK :=
    if isBranchy tail then (arms tail).all fun (cs?, v) => (cs?.getD []).all plain && groupOK v
    else isChoice tail && groupOK tail
  if cls.all plain && tailOK then some (cls, tail) else none

/-- A function's name as written: a method's function `C$M` as `C.M`, and
    `F$all` as `F` (#283). -/
def shownFnName (n : String) : String :=
  let n := if n.endsWith "$all" then String.ofList (n.toList.take (n.length - 4)) else n
  if n.startsWith "$" then n else (n.replace "::" ".").replace "$" "."

/-- The calls of `g` in `e` (its consumer's code, #246) as `$rec(args)`. -/
def markRec (g : String) : SExpr → SExpr :=
  mapE fun
    | .app p (.ident _ h) as _ => if h == g then some (.app p (.ident p "$rec") as false) else none
    | _ => none

/-- Replace each call of a function of `mv` by `$inline(F, template, args…)`,
    each with its own call site (`n`, the sites so far); a call of one of
    `loops` by `$loop(F, …)` (#246). -/
partial def inlineCalls (mv : List (String × MFn)) (e : SExpr) (recs : List String := [])
    (loops : List String := []) (clash : List (String × List String) := [])
    (inDflt : List (String × String) := []) : StateT Nat (Except String) SExpr := do
  -- (`inDflt`: the defaults being inlined, function and parameter, #283)
  let go := fun x => inlineCalls mv x recs loops clash inDflt
  match e with
  | .app p (.ident q g) as br =>
    match mv.lookup g with
    | some f =>
      -- (as at a call: several arguments to a single array parameter, and
      -- one tuple argument to several parameters, #134, #140)
      -- (named parameters, #283: none of that, as at such a call)
      let hasNamed := f.params.any (·.named)
      let posPs := f.params.filter (!·.named)
      let posAs := as.filter fun | .decl _ n _ _ _ => !n.startsWith "?" | _ => true
      let namedAs : List (Pos × String × SExpr) := as.filterMap fun
        | .decl ap n _ _ x => if n.startsWith "?" then some (ap, (n.drop 1).toString, x) else none
        | _ => none
      -- (a method's function, #283: its receiver first, then the arguments
      -- as a method's; no array form for a method, as at its call)
      let selfP := match f.params with | sp :: _ => sp.name == "$Self" | _ => false
      let off := if selfP then 1 else 0
      let arrayParam := !hasNamed && !selfP && match f.params with | [sp] => (match sp.ty with | .arr _ => true | _ => false) | _ => false
      let tupleArg := !hasNamed && as.length == 1 + off && f.params.length ≥ 2 + off
      -- (one tuple argument, no named one, to several positional parameters:
      -- expanded, as at a call)
      let tupleNamed := hasNamed && namedAs.isEmpty && as.length == 1 + off && posPs.length ≥ 2 + off
      if hasNamed then
        if posAs.length != posPs.length && !tupleNamed then
          throw s!"{p.show}: {shownFnName g} takes {posPs.length - off} positional argument(s), found {posAs.length - off}"
        for ((ap, n, _), i) in namedAs.zipIdx do
          if !(f.params.any fun sp => sp.named && sp.name == n) then throw s!"{ap.show}: {shownFnName g} has no parameter ?{n}"
          if (namedAs.take i).any (·.2.1 == n) then throw s!"{ap.show}: ?{n} is given twice"
        for sp in f.params do
          if sp.named && sp.default.isNone && !namedAs.any (·.2.1 == sp.name) then
            throw s!"{p.show}: {shownFnName g} needs the argument ?{sp.name}, which has no default"
      else
        if as.length != f.params.length && !arrayParam && !tupleArg then
          throw s!"{p.show}: {shownFnName g} takes {f.params.length - off} argument(s), found {as.length - off}"
        if !namedAs.isEmpty then
          throw s!"{p.show}: {shownFnName g} has no named parameters"
      if br != f.fx.contains "decides" then
        throw (if br then s!"{p.show}: {shownFnName g} is not <decides>: call it with {shownFnName g}(…)"
          else s!"{p.show}: {shownFnName g} is <decides>: call it with {shownFnName g}[…]")
      -- (with named parameters, the positional arguments' then the named
      -- ones' values, as evaluated)
      let as' ← if hasNamed then pure [] else as.mapM go
      let posVals ← if hasNamed then posAs.mapM go else pure []
      let namedVals ← if hasNamed then namedAs.mapM (fun (_, _, x) => go x) else pure []
      -- (a recursive one: the array of its values, computed at the call)
      if recs.contains g && !loops.contains g then
        return .app p (.ident p "$each") [.app p (.ident q s!"{g}$all") as' false] false
      let site ← modifyGet fun n => (n, n + 1)
      if site ≥ 2000 then
        throw s!"{p.show}: more than 2000 calls of functions with several values to inline: nested calls multiply them (#235)"
      let tag (n : String) : String := s!"${g.replace "::" "_"}_{n}_{site}"
      let ren := (f.params.map (·.name) ++ localsOf f.body).eraseDups.map fun n => (n, tag n)
      -- (a generic one's type parameters renamed for this site, #235: its
      -- parameters are bound together, the type arguments inferred from
      -- the arguments as at a call, `$params`, which then names them for
      -- the written types after)
      let ρ : List (String × String) := f.tparams.map fun tp => (tp.name, s!"$tp{site}_{tp.name}")
      let tyOf (t : STy) : Option STy := some (styRename ρ t)
      let tmark : List SExpr := (if ρ.isEmpty then [] else
        [.app q (.ident q "$tparams") (.ident q g :: (ρ.zip f.tparams).map fun ((_, n), tp) =>
          SExpr.tuple q [.ident q n, .ident q tp.constraint]) false]) ++
        -- (the names its body uses from outside, checked not in scope here)
        (match clash.lookup g with
         | some us => [.app q (.ident q "$freeNames") (.ident q g :: us.map (SExpr.ident q ·)) false]
         | none => [])
      -- (with named parameters: the positional ones, then the named ones
      -- given, as written, then the defaults of those omitted, in order,
      -- each in its own context, `$paramDefault`, as at a call)
      let pdOf (sp : SParam) : SExpr := .decl q (tag sp.name) (tyOf sp.ty) false (.ident q "$arg")
      let dflts ← if !hasNamed then pure [] else
        f.params.zipIdx.filterMapM fun (sp, k) => do
          match sp.default with
          | some d =>
            if !sp.named || namedAs.any (·.2.1 == sp.name) then return none
            -- (one that calls `g` again omitting it: as at a call)
            if inDflt.contains (g, sp.name) then
              throw s!"{p.show}: the default of ?{sp.name} of {shownFnName g} uses itself (a call of {shownFnName g} that omits ?{sp.name})"
            let d' ← inlineCalls mv (renameTypes ρ d) recs loops clash ((g, sp.name) :: inDflt)
            let earlier := (f.params.take k).map fun e => SExpr.tuple q [.ident q e.name, .ident q (tag e.name)]
            return some (.decl q (tag sp.name) (tyOf sp.ty) false
              (.app q (.ident q "$paramDefault") [.ident q g, .ident q sp.name, .block q earlier, d'] false))
          | none => return none
      let (pds, unpack, as'') : List SExpr × List SExpr × List SExpr :=
        if tupleNamed then
          let t := tag "$tuple"
          let tps := posPs.drop off
          ((posPs.take off).map pdOf ++ [.decl q t (tyOf (.tup (tps.map (·.ty)))) false (.ident q "$arg")],
            (tps.zipIdx.map fun (sp, i) =>
              SExpr.decl q (tag sp.name) (tyOf sp.ty) false (.app q (.ident q t) [.int q (i : Int)] false)) ++ dflts,
            posVals)
        else if hasNamed then
          (posPs.map pdOf ++ namedAs.filterMap (fun (_, n, _) => (f.params.find? (·.name == n)).map pdOf), dflts,
            posVals ++ namedVals)
        else if as.length == f.params.length then
          (f.params.map fun sp => SExpr.decl q (tag sp.name) (tyOf sp.ty) false (.ident q "$arg"), [], as')
        else if arrayParam then
          (f.params.map fun sp => SExpr.decl q (tag sp.name) (tyOf sp.ty) false (.ident q "$arg"), [],
            [.arrayLit p as'])
        else
          -- (the tuple bound once, its elements into the parameters; a
          -- method's receiver first)
          let t := tag "$tuple"
          let tps := f.params.drop off
          ((f.params.take off).map pdOf ++ [.decl q t (tyOf (.tup (tps.map (·.ty)))) false (.ident q "$arg")],
            (tps.zipIdx.map fun (sp, i) =>
              SExpr.decl q (tag sp.name) (tyOf sp.ty) false (.app q (.ident q t) [.int q (i : Int)] false)), as')
      -- (one taken lazily, #246: its parameters, its clauses and its last
      -- expression, its own calls marked, for its consumer to run)
      if loops.contains g then
        let some (cls, tail) := loopShape? g (mv.map (·.1)) (renameTypes ρ (renameE ren f.body))
          | throw s!"{p.show}: internal: the shape of {g} (#246)"
        let ps := f.params.map fun sp => SExpr.ident q (tag sp.name)
        return .app p (.ident p "$loop") (.ident q g :: .block q (tmark ++ pds ++ unpack) :: .block q ps :: .block q cls ::
          .decl q (tag "$r") (tyOf f.ret) false (markRec g tail) :: as'') false
      let body ← go (renameTypes ρ (renameE ren f.body))
      let ss := stmtsOf body
      let r := tag "$r"
      let (init, last) := (ss.dropLast, ss.getLast?)
      let (init, res) : List SExpr × SExpr := match last with
        | some (.decl q2 x t v rhs) => (init ++ [.decl q2 x t v rhs], .ident q2 x)
        | some l => (init, l)
        | none => (init, .tuple q [])
      let tmpl := SExpr.block q (tmark ++ pds ++ unpack ++ init ++ [.decl q r (tyOf f.ret) false res])
      return .app p (.ident p "$inline") (.ident q g :: tmpl :: as'') false
    | none => return .app p (← go (.ident q g)) (← as.mapM go) br
  | .str p ps => return .str p (← ps.mapM fun | .code c => do return .code (← go c) | t => pure t)
  | .app p g as b => return .app p (← go g) (← as.mapM go) b
  | .member p x m => return .member p (← go x) m
  | .query p x => return .query p (← go x)
  | .neg p x => return .neg p (← go x)
  | .notE p x => return .notE p (← go x)
  | .bin p o a b => return .bin p o (← go a) (← go b)
  | .cmp p a r => return .cmp p (← go a) (← r.mapM fun (o, b) => do return (o, ← go b))
  | .andE p a b => return .andE p (← go a) (← go b)
  | .orE p a b => return .orE p (← go a) (← go b)
  | .range p a b => return .range p (← go a) (← go b)
  | .tuple p es => return .tuple p (← es.mapM go)
  | .block p es => return .block p (← es.mapM go)
  | .arrayLit p es => return .arrayLit p (← es.mapM go)
  | .optionLit p x => return .optionLit p (← go x)
  | .logicLit p x => return .logicLit p (← go x)
  | .ite p cs t e' => return .ite p (← cs.mapM go) (← go t) (← e'.mapM go)
  | .forE p cs b => return .forE p (← cs.mapM go) (← go b)
  | .gen p x i src => return .gen p x i (← go src)
  | .loop p b => return .loop p (← go b)
  | .ret p x => return .ret p (← x.mapM go)
  | .caseE p sc arms => return .caseE p (← go sc) (← arms.mapM fun (pt, v) => do
      return (← pt.mapM go, ← go v))
  | .decl p n t v x => return .decl p n t v (← go x)
  | .set p l o r => return .set p (← go l) o (← go r)
  | .construct p n ts fs => return .construct p n ts (← fs.mapM fun
      | .decl q fn t v x => do return .decl q fn t v (← go x)
      | a => go a)
  | .mapLit p kvs => return .mapLit p (← kvs.mapM fun (k, v) => do return (← go k, ← go v))
  | .structDef p tps fs => return .structDef p tps (← fs.mapM fun (n, t, d, v) => do return (n, t, ← d.mapM go, v))
  | e => return e

mutual
/-- The array of an expression's values, for a `$all` body (#235): a choice
    concatenates its alternatives' arrays, an `if` with choices in its
    branches picks a branch's, and any other expression is the array of the
    values of its own clauses (`gensOf`): of its value, empty when it fails,
    and through the choices and calls of functions with several values
    (marked `$each`) inside it. So an alternative that fails, or whose
    argument does, gives no values, and the others still do. At the written
    type `ty`, when there is one. -/
partial def arrOfE (ty : Option STy := none) : SExpr → SExpr
  | .app p (.ident _ "$choice") as false =>
    match as with
    | [a] => arrOfE ty a
    | _ => .app p (.ident p "Concatenate") (as.map (arrOfE ty)) false
  | .ite p cs t (some e) => .ite p cs (arrOfE ty t) (some (arrOfE ty e))
  | a =>
    let p := a.pos
    let site := s!"a{p.line}_{p.col}"
    let v := s!"$a{p.line}_{p.col}"
    .forE p (gensOf site [.decl p v ty false a]) (.ident p v)

/-- Clauses for a `for` that goes through all their values (#235): each
    choice a generator over the array of its alternatives' values, each
    call of a recursive function with several values one over its array.
    Names made include `site`, so that nested ones differ. -/
partial def gensOf (site : String) (cs : List SExpr) : List SExpr :=
  let nm (q : Pos) : String := s!"$e{sitePart site}{q.line}_{q.col}"
  (prepare cs (site := site)).flatMap fun c => match binding? c with
    | some { pos := q, name := x, ty := ty, alts := as, branchy := none, each := none, .. } =>
      let src := arrOfE ty (.app q (.ident q "$choice") as false)
      match ty with
      | none => [.gen q x none src]
      | some t => [.gen q (nm q) none src, .decl q x (some t) false (.ident q (nm q))]
    | some { pos := q, name := x, ty := ty, branchy := some i, .. } =>
      match ty with
      | none => [.gen q x none (arrOfE none i)]
      | some t => [.gen q (nm q) none (arrOfE (some t) i), .decl q x (some t) false (.ident q (nm q))]
    | some { pos := q, name := x, ty := ty, each := some a, .. } =>
      match ty with
      | none => [.gen q x none a]
      | some t => [.gen q (nm q) none a, .decl q x (some t) false (.ident q (nm q))]
    | _ => [c]
end

/-- Each call of a function of `mvs` marked as the array of its values,
    `$each(F$all(args))`, also in the arguments of others. -/
partial def markAll (mvs : List String) : SExpr → SExpr :=
  mapE fun
    | .app p (.ident q g) as _ =>
      if mvs.contains g then
        some (.app p (.ident p "$each") [.app p (.ident q s!"{g}$all") (as.map (markAll mvs)) false] false)
      else none
    | _ => none

/-- The body of `F$all`, the array of `F`'s values in order (#235): one
    `for` over its clauses (`gensOf`), whose value is `F`'s, at its result
    type `ret`. (`F` is effect-free, so evaluating the clauses in this order
    changes nothing.) -/
def allBody (mvs : List String) (ret : STy) (b : SExpr) : SExpr :=
  let ss := stmtsOf (markAll mvs b)
  let p := b.pos
  let (cs, v) : List SExpr × SExpr := match ss.getLast? with
    | some (.decl q x _ _ _) => (ss, .ident q x)
    | some l => (ss.dropLast ++ [.decl l.pos "$val" (some ret) false l], .ident l.pos "$val")
    | none => ([], .tuple p [])
  .forE p (gensOf "" cs) v

/-- A name of `mv` used other than as a call's head: as a function value. -/
partial def valueUse? (mv : List String) : SExpr → Option (Pos × String)
  | .app _ (.ident _ _) as _ => as.findSome? (valueUse? mv)
  | .ident p n => if mv.contains n then some (p, n) else none
  | e =>
    let kids : List SExpr := match e with
      | .str _ ps => ps.filterMap fun | .code c => some c | _ => none
      | .app _ g as _ => g :: as
      | .member _ x _ | .query _ x | .neg _ x | .notE _ x | .optionLit _ x | .logicLit _ x | .loop _ x
      | .gen _ _ _ x | .decl _ _ _ _ x => [x]
      | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b | .set _ a _ b => [a, b]
      | .cmp _ a r => a :: r.map (·.2)
      | .tuple _ es | .block _ es | .arrayLit _ es | .construct _ _ _ es => es
      | .ite _ cs t e' => cs ++ [t] ++ e'.toList
      | .forE _ cs b => cs ++ [b]
      | .ret _ x => x.toList
      | .caseE _ sc arms => sc :: arms.flatMap fun (pt, v) => pt.toList ++ [v]
      | .mapLit _ kvs => kvs.flatMap fun (k, v) => [k, v]
      | .structDef _ _ fs => fs.filterMap (·.2.2.1)
      | _ => []
    kids.findSome? (valueUse? mv)

/-- (#246) A lazily taken call, where the first success is taken, whose
    clauses, conditions or calls of itself have effects: compiled as a
    function of its own, recursive, so that each alternative and each call
    of itself is a failure context of its own, undone with its values as
    the Verse Calculus does. It takes the function's parameters and the
    consumer's names that the clauses after the call use (`args`, at the
    consumer), and gives, at the first success of those clauses, the names
    they bind and the final values of the `var`s they set (`binds`, then
    `sets`, then `true`). -/
structure FirstLift where
  key : String
  pos : Pos
  name : String
  params : List SParam
  specs : List String
  ret : STy
  body : SExpr
  binds : List String
  sets : List String
  args : List SExpr
  /-- The names of `binds` that are `var`s, bound so again. -/
  varBinds : List String := []
  deriving Inhabited

/-- The body of a `FirstLift` (#246): the function's clauses, then the first
    success of its last expression, each value followed by the consumer's
    clauses after the call (`rest`, the value bound to `b` first) and the
    tuple of what they bind, each call of itself a call of `helper` with the
    captured names after its arguments. The `var`s the clauses set are
    copied first from parameters named `m$in`. -/
def firstBody (helper : String) (p : Pos) (b : String) (bty : Option STy) (cls : List SExpr) (tail : SExpr)
    (rest : List SExpr) (binds : List String) (sets : List (String × STy)) (caps : List SExpr)
    (ret : Option STy := none) : SExpr :=
  let tup : SExpr := .tuple p (binds.map (SExpr.ident p ·) ++ sets.map (fun (m, _) => SExpr.ident p m) ++
    [.ident p "true"])
  let alt (a : SExpr) : SExpr := match a with
    | .app q (.ident _ "$rec") as false => .app q (.ident q helper) (as ++ caps) true
    | a =>
      -- (the value at the function's result type, then at the binding's)
      let v := match ret with
        | some t => SExpr.app a.pos (.ident a.pos "$first") [.block a.pos [.decl a.pos s!"{b}$v" (some t) false a,
            .ident a.pos s!"{b}$v"]] false
        | none => a
      -- (`$firstP`: `first{…}` of clauses that are lifted already, the
      -- consumer's, which lifting again would bind twice)
      .app a.pos (.ident a.pos "$firstP") [.block a.pos ([.decl a.pos b bty false v] ++ rest ++ [tup])] false
  let group (v : SExpr) : SExpr := match alts? v with
    | some as => mk v.pos (as.map alt)
    | none => alt v
  let rec chain : List (Option (List SExpr) × SExpr) → SExpr
    | [] => .tuple p []
    | [(_, v)] => group v
    | (some cs, v) :: more => .ite p cs (group v) (some (chain more))
    | (none, v) :: _ => group v
  let tail' := if isBranchy tail then chain (arms tail) else group tail
  let copies := sets.map fun (m, t) => SExpr.decl p m (some t) true (.ident p s!"{m}$in")
  .block p (copies ++ cls ++
    [.app p (.ident p "$first") [.block p [.decl p "$R" none false tail', .ident p "$R"]] false])

/-- The functions a call of which may have several values: (not `Main` or
    the entry expression, which nothing calls in a failure context, nor
    `<suspends>` functions, which cannot run in one). -/
def multiCandidates (tops : List STop) : List (String × MFn) :=
  tops.filterMap fun
    | .fn p n ps tps fx r b =>
      if n == "Main" || n == "$Do" || fx.contains "suspends" then none else some (n, ⟨p, ps, tps, fx, r, b⟩)
    | _ => none

/-- Which of `fns` have several values, also through the calls of ones that
    have them, where the body itself does not take their values. -/
def multiValued (fns : List (String × MFn)) : List String := Id.run do
  let mut mv : List String := []
  let mut changed := true
  while changed do
    changed := false
    for (n, f) in fns do
      let ss := stmtsOf (markCalls mv f.body)
      if !mv.contains n && (hasChoice ss || ss.any liftsHere) then
        mv := mv ++ [n]; changed := true
  return mv

/-- The name of the function a method `m` of class `c` with several values
    becomes (#283). -/
def methodFnName (c m : String) : String := s!"{c}${m}"

/-- A method's body with the names of its class's members qualified by
    `Self` (#283): `isMethod`, `isMember` and `free` say which names. -/
partial def qualMembers (isMethod isMember free : String → Bool) (e : SExpr) : SExpr :=
  let go := qualMembers isMethod isMember free
  mapE (fun
    | .app p (.ident q n) args br =>
      if free n && isMethod n then some (.app p (.member q (.ident q "Self") n) (args.map go) br) else none
    | .ident p n => if free n && isMember n then some (.member p (.ident p "Self") n) else none
    | _ => none) e

/-- `e` with the calls of `names`, by name or as a member, as calls of
    `$h`: what is left of the names is then a use as a value (#283). -/
partial def eraseCallHeads (names : List String) (e : SExpr) : SExpr :=
  let go := eraseCallHeads names
  mapE (fun
    | .app p (.ident q x) args br => if names.contains x then some (.app p (.ident q "$h") (args.map go) br) else none
    | .app p (.member q r x) args br =>
      if names.contains x then some (.app p (.ident q "$h") ((r :: args).map go) br) else none
    | _ => none) e

/-- The calls of the methods `sel` (name, class) in `e` as calls of their
    functions (#283): `R.M(args)` as `C$M(R, args)`, and in the body of a
    class `inC` below `C` (`anc` gives a class's ancestors), `M(args)` as
    `C$M(Self, args)`. -/
partial def rwMethodCalls (anc : String → List String) (sel : List (String × String)) (inC : Option String)
    (e : SExpr) : SExpr :=
  let rw := rwMethodCalls anc sel inC
  mapE (fun
    | .app p (.member q recv m) args br =>
      match sel.lookup m with
      -- (`(super:)M(…)` too: `M` is overridden nowhere, so it is `C`'s)
      | some c =>
        let recv := match recv with | .ident r "(super:)" => .ident r "Self" | r => rw r
        some (.app p (.ident q (methodFnName c m)) (recv :: args.map rw) br)
      | none => none
    | .app p (.ident q m) args br =>
      match sel.lookup m, inC with
      | some c, some d => if (anc d).contains c then
          some (.app p (.ident q (methodFnName c m)) (.ident q "Self" :: args.map rw) br) else none
      | _, _ => none
    | _ => none) e

/-- Methods with several values (#283), as top-level functions that take
    `Self` explicitly, so that everything functions with several values
    have applies: `C$M($Self:C, params…)`, its body with the names of `C`'s
    members (and its supers') qualified by `Self`, then `Self` renamed;
    `R.M(args)` becomes `C$M(R, args)` (the receiver first, once), and in
    `C`'s bodies and its subclasses' `M(args)` and `Self.M(args)` become
    `C$M(Self, args)`. Inlining has no types, so `R.M` must name that
    method whatever `R` is: such a method's name is no other class's or
    interface's member, no top-level name and no parameter or local, its
    class is not generic, and it is not abstract, an override, generic,
    `<suspends>`, or a user of `(super:)`. Those methods that turn out to
    have several values are taken out of their class. -/
def methodFns (tops : List STop) (reserved : List String := []) : Except String (List STop) := do
  let classes := tops.filterMap fun
    | .classDef _ n tps _ pa ii fs _ ms => some (n, (pa, ii, fs, ms, tps))
    | _ => none
  if classes.isEmpty then return tops
  let parentNames (pa : List STy) : List String := pa.filterMap fun | .name n => some n | .app n _ => some n | _ => none
  let rec ancestors (fuel : Nat) (c : String) : List String := match fuel with
    | 0 => [c]
    | f + 1 => c :: (((classes.lookup c).map fun (pa, _) => (parentNames pa).flatMap (ancestors f)).getD [])
  let anc (c : String) : List String := (ancestors (classes.length + 1) c).eraseDups
  -- (every member name of `c`, inherited ones too)
  let members (c : String) : List String := (anc c).flatMap fun d =>
    match classes.lookup d with
    | some (_, _, fs, ms, _) => fs.map (·.1) ++ ms.filterMap fun | .fn _ m .. => some m | _ => none
    | none => []
  let allMethods : List String := classes.flatMap fun (_, (_, _, _, ms, _)) => ms.filterMap fun | .fn _ m .. => some m | _ => none
  -- (struct fields and enumerators too, and the members of built-in types
  -- and of the prelude, `reserved`: `R.M` may be any of them)
  let allFields : List String := classes.flatMap (fun (_, (_, _, fs, _, _)) => fs.map (·.1)) ++
    tops.flatMap (fun
      | .const _ _ _ (.structDef _ _ fs) => fs.map (·.1)
      | .const _ _ _ (.enumDef _ vs _) => vs
      | _ => []) ++ reserved
  let topNames : List String := tops.filterMap fun | .fn _ n .. | .const _ n .. | .classDef _ n .. => some n
  let localBinders : List String := tops.flatMap fun
    | .fn _ _ ps _ _ _ b => ps.map (·.name) ++ localsOf b
    | .classDef _ _ _ _ _ _ _ _ ms => ms.flatMap fun | .fn _ _ ps _ _ _ b => ps.map (·.name) ++ localsOf b | _ => []
    | _ => []
  let superCall (b : SExpr) : Bool := anyE (fun | .member _ (.ident _ "(super:)") _ => true | _ => false) b
  -- (why a method cannot become a function, if it cannot)
  let whyNot (ii : Bool) (tps : List TParam) : STop → Option String
    | .fn _ n _ mtps fx _ b =>
      if n.startsWith "$" || n.startsWith "(" || fx.contains "$abstract" then some ""
      else if ii then some "it is an interface's"
      else if !tps.isEmpty then some "its class is generic"
      else if !mtps.isEmpty then some "it is generic"
      else if fx.contains "suspends" then some "it is <suspends>"
      else if fx.contains "override" || (allMethods.filter (· == n)).length != 1 then
        some s!"another class or interface has a method {n} too (an override, an overridden one, or another), so a call R.{n}(…) cannot be known to be this one where it is inlined, before types are checked"
      else if allFields.contains n || topNames.contains n || localBinders.contains n then
        some s!"{n} is also the name of a field, an enumerator, a member of a built-in type, a top-level name, a parameter or a local"
      else if superCall b then some "it uses (super:)"
      else none
    | _ => some ""
  -- (the candidates: class, method)
  let cands : List (String × STop) := classes.flatMap fun (c, (_, ii, _, ms, tps)) =>
    ms.filterMap fun m => if (whyNot ii tps m).isNone then some (c, m) else none
  let owner : List (String × String) := cands.filterMap fun | (c, .fn _ n ..) => some (n, c) | _ => none
  let rw := rwMethodCalls anc
  -- (a method's body as the function's: its members qualified by `Self`,
  -- then `Self` the parameter `$Self`)
  let fnOf (sel : List (String × String)) (c : String) : STop → Option STop
    | .fn p m ps _ fx r b =>
      let mem := members c
      let isMethodName := fun n => (anc c).any fun d => match classes.lookup d with
        | some (_, _, _, ms, _) => ms.any fun | .fn _ x .. => x == n | _ => false
        | none => false
      let bound := ps.map (·.name) ++ localsOf b
      let free := fun n => !bound.contains n && n != "Self"
      let qual := qualMembers isMethodName mem.contains free
      -- (now `M(…)` is `Self.M(…)`; then the calls of the selected ones;
      -- a parameter's default too, which sees the method's fields)
      let fix := fun e => renameE [("Self", "$Self")] (rw sel (some c) (qual e))
      let ps' := ps.map fun sp => { sp with default := sp.default.map fix }
      some (.fn p (methodFnName c m) ({ name := "$Self", ty := .name c } :: ps') [] fx r (fix b))
    | _ => none
  -- (which of them have several values: with every candidate's calls
  -- rewritten, the functions' fixpoint)
  let all := cands.map fun (c, m) => (c, m)
  let trial : List STop := tops.map (fun
      | .fn p n ps tps fx r b => .fn p n ps tps fx r (rw owner none b)
      | .classDef p n tps sp pa ii fs ov ms => .classDef p n tps sp pa ii fs ov (ms.map fun
          | .fn p2 m ps fx2 x r b => .fn p2 m ps fx2 x r (rw owner (some n) b)
          | s => s)
      | t => t) ++ all.filterMap fun (c, m) => fnOf owner c m
  let mv := multiValued (multiCandidates trial)
  -- (one that has several values but cannot become a function: refused,
  -- saying why)
  for (c, (_, ii, _, ms, tps)) in classes do
    for m in ms do
      if let (some why, .fn p n _ _ _ _ b) := (whyNot ii tps m, m) then
        if why != "" then
          let ss := stmtsOf (markCalls mv (rw owner (some c) b))
          if hasChoice ss || ss.any liftsHere then
            throw s!"{p.show}: {c.replace "::" "."}.{n} has several values, but {why}: such methods are not supported yet (#283)"
  let sel := owner.filter fun (m, c) => mv.contains (methodFnName c m)
  if sel.isEmpty then return tops
  -- (a parameter or local named like a member: refused, as in the class,
  -- since the body leaves it)
  for (c, m) in cands do
    if let .fn p n ps _ _ _ b := m then
      if sel.any (fun (m', c') => m' == n && c' == c) then
        let mem := members c
        if let some sp := ps.find? (mem.contains ·.name) then
          throw s!"{p.show}: parameter '{sp.name}' of {n} is already a field or method of {c.replace "::" "."}; Verse does not allow shadowing"
        if let some (x, q) := (localDecls b).find? (mem.contains ·.1) then
          throw s!"{q.show}: '{x}' is already a field or method of {c.replace "::" "."}; Verse does not allow shadowing"
  -- (the program with those methods out of their classes and their calls
  -- rewritten, and their functions)
  let out := tops.map fun
    | .fn p n ps tps fx r b => .fn p n ps tps fx r (rw sel none b)
    | .const p n ty e => .const p n ty (rw sel none e)
    | .classDef p n tps sp pa ii fs ov ms =>
      .classDef p n tps sp pa ii (fs.map fun (f, t, d, v) => (f, t, d.map (rw sel (some n)), v)) ov (ms.filterMap fun
        | .fn p2 m ps fx2 x r b => if sel.any (fun (m', c) => m' == m && c == n) then none
            else some (.fn p2 m ps fx2 x r (rw sel (some n) b))
        | s => some s)
  -- (what is left of their names is a use as a value: refused, as for a
  -- function's; a name of theirs is nothing else's)
  let valueUse (e : SExpr) : Option (Pos × String) := Id.run do
    let mut r := none
    let e := eraseCallHeads (sel.map (·.1)) e
    for m in sel.map (·.1) do
      if r.isNone && anyE (fun | .member _ _ x | .ident _ x => x == m | _ => false) e then
        r := some (e.pos, m)
    return r
  for t in out do
    let bodies : List SExpr := match t with
      | .fn _ _ ps _ _ _ b => b :: ps.filterMap (·.default)
      | .const _ _ _ e => [e]
      | .classDef _ _ _ _ _ _ fs _ ms => fs.filterMap (·.2.2.1) ++ ms.flatMap fun
          | .fn _ _ ps _ _ _ b => b :: ps.filterMap (·.default)
          | _ => []
    for b in bodies do
      if let some (_, m) := valueUse b then
        let c := (sel.lookup m).getD ""
        let b := eraseCallHeads (sel.map (·.1)) b
        let p := ((stmtsOf b).find? (anyE fun | .member _ _ x | .ident _ x => x == m | _ => false)).map (·.pos) |>.getD b.pos
        throw s!"{p.show}: {c.replace "::" "."}.{m} has several values, so it cannot be used as a function value (#235, #283)"
  return out ++ all.filterMap fun (c, m) => match m with
    | .fn _ n .. => if sel.any (fun (m', c') => m' == n && c' == c) then fnOf sel c m else none
    | _ => none

/-- The functions of the program that have several values, inlined at their
    calls (see above); the program unchanged when there are none. Also
    whether some are taken lazily (#246), whose consumers need a class of
    stack cells. -/
def inlineMulti (tops : List STop) (reserved : List String := []) : Except String (List STop × Bool) := do
  -- (methods with several values as functions first, #283; `reserved`:
  -- the members of built-in types and of the prelude)
  let tops ← methodFns tops reserved
  let fns := multiCandidates tops
  let mv := multiValued fns
  if mv.isEmpty then return (tops, false)
  let mfs := fns.filter (mv.contains ·.1)
  -- (every name the program binds: parameters, locals, fields, methods)
  let binders : List String := (tops.flatMap fun
    | .fn _ _ ps _ _ _ b => ps.map (·.name) ++ localsOf b
    | .const _ _ _ (.structDef _ _ fs) => fs.map (·.1)
    | .classDef _ _ _ _ _ _ fs _ ms => fs.map (·.1) ++ ms.flatMap fun
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
  let loops : List String := recs.filter fun g =>
    match mfs.lookup g with
    | some f => (callees.lookup g).getD [] == [g] && (loopShape? g mv f.body).isSome
    | none => false
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
    let some f := mfs.lookup g | continue
    let why (w : String) : String :=
      s!"{f.pos.show}: {shownFnName g} has several values and is recursive, or called by a recursive one, {w}: such a function must be <computes>, keep no local state, and reach nothing that prints or calls Err(), as all its values are computed at a call (#235)"
    if !f.fx.contains "computes" then throw (why "and it is not <computes>")
    if anyE (fun | .set .. | .decl _ _ _ true _ => true | _ => false) f.body then
      throw (why "and it has a var or a set")
  for (n, f) in mfs do
    if (fns.filter (·.1 == n)).length > 1 then
      throw s!"{f.pos.show}: {shownFnName n} has several values and is overloaded: such functions are not supported yet (#235)"
    if f.params.any (·.named) && (recs.contains n || needAll.contains n || !f.tparams.isEmpty) then
      let what := if recs.contains n then "recursive" else if needAll.contains n then
        "called by a recursive one (so its values are computed at the call, F$all)" else "generic"
      throw s!"{f.pos.show}: {shownFnName n} has several values and named parameters, and is {what}: such functions are not supported yet (#235, #283)"
    if anyE (fun | .ret .. => true | _ => false) f.body then
      throw s!"{f.pos.show}: {shownFnName n} has several values and a return, which would leave its caller once inlined (#235)"
    if (stmtsOf f.body).any (fun | .app _ (.ident _ "$defer") _ _ => true | _ => false) then
      throw s!"{f.pos.show}: {shownFnName n} has several values and a defer:, which would run in its caller's clauses once inlined: not supported yet (#235)"
    -- (its body is inlined where other names may be in scope: so neither
    -- its name nor a name its body uses from outside may be bound anywhere)
    if binders.contains n then
      throw s!"{f.pos.show}: {n} has several values, and {n} is also the name of a parameter, local, field or method: rename one, as calls of {n} are inlined (#235)"
    -- (a name its body uses from outside that is bound somewhere too is
    -- checked where the body is inlined, `$freeNames`, #283)
  -- (no use as a value)
  let defaults (ps : List SParam) : List SExpr := ps.filterMap (·.default)
  let bodies : List SExpr := tops.flatMap fun
    | .fn _ _ ps _ _ _ b => b :: defaults ps
    | .const _ _ _ e => [e]
    | .classDef _ _ _ _ _ _ fs _ ms => fs.filterMap (·.2.2.1) ++ ms.flatMap fun
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
  let go (e : SExpr) : StateT Nat (Except String) SExpr := inlineCalls mfs e recs loops clash
  let goPs (ps : List SParam) : StateT Nat (Except String) (List SParam) :=
    ps.mapM fun sp => do return { sp with default := ← sp.default.mapM go }
  let (tops', _) ← (tops.filterMapM (m := StateT Nat (Except String)) fun t => do
    match t with
    | .fn p n ps tps fx r b =>
      -- (its own name kept, so that messages name it: nothing calls it)
      if mv.contains n then
        return some (.fn p n ps tps fx r (checkBody b))
      return some (.fn p n (← goPs ps) tps fx r (← go b))
    | .const p n ty e => return some (.const p n ty (← go e))
    | .classDef p n tps sp pa ii fs ov ms =>
      let fs' ← fs.mapM fun (fn, t, d, v) => do return (fn, t, ← d.mapM go, v)
      let ms' ← ms.mapM fun
        | .fn p2 n2 ps2 tps2 fx2 r2 b2 => do return STop.fn p2 n2 (← goPs ps2) tps2 fx2 r2 (← go b2)
        | m => pure m
      return some (.classDef p n tps sp pa ii fs' ov ms')).run 0
  -- (`F$all` for each that needs one: the array of its values)
  let alls : List STop := needAll.filterMap fun g => (mfs.lookup g).map fun f =>
    .fn f.pos s!"{g}$all" f.params f.tparams (f.fx.filter (· != "decides")) (.arr f.ret) (allBody needAll f.ret f.body)
  return (tops' ++ alls, !loops.isEmpty)

end OpenVerse.Front.Choice
