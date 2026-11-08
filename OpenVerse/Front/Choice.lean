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

def binding? : SExpr → Option Binding
  | .decl p x ty false (.app _ (.ident _ "$choice") as false) => some ⟨p, x, ty, as, none⟩
  | .decl p x ty false (.app _ (.ident _ "$choiceAt") (l :: as) false) => some ⟨p, x, ty, as, some l⟩
  | _ => none

/-- The indices of a `set` path bound to names, in order (unless literals),
    and the path with those names in their places: `set` evaluates them
    before the new value. -/
partial def hoistPath (q : Pos) (l : SExpr) : List SExpr × SExpr :=
  let nm (n : Nat) : String := s!"$i{q.line}_{q.col}_{n}"
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
    | e => ([], e, n)
  let (h, l', _) := go 0 l
  (h, l')

/-- `set L op= R` whose `R` needs code before it (a choice, or lifted
    operands): `L`'s indices, then for `op=` its old value, then that code,
    as `set` evaluates. `$withOld(O, R)` tells the elaborator that the old
    value is already in `O`. The result: the clauses before, the old value's
    name, and the path. -/
def setPrefix (q : Pos) (l : SExpr) (op : Option String) : List SExpr × Option String × SExpr :=
  let (h, l') := hoistPath q l
  match op with
  | none => (h, none, l')
  | some _ =>
    let o := s!"$o{q.line}_{q.col}"
    (h ++ [.decl q o none false l'], some o, l')

/-- The new value of a `set` whose old one is in `o?`. -/
def withOld (q : Pos) (o? : Option String) (r : SExpr) : SExpr :=
  match o? with
  | some o => .app q (.ident q "$withOld") [.ident q o, r] false
  | none => r

/-- `set L op= a | b` with the choice bound first, as `set` evaluates (Book
    of Verse §3.5): the indices of `L`'s path, then for `op=` the old value,
    then the choice. For `=`, the alternatives take `L`'s type. -/
def setClauses (p : Pos) (l : SExpr) (op : Option String) (as : List SExpr) (q : Pos) :
    List SExpr × SExpr :=
  let (h, o?, l') := setPrefix q l op
  let c := s!"$c{q.line}_{q.col}"
  let choice : SExpr := match op with
    | none => .app q (.ident q "$choiceAt") (l' :: as) false
    | some _ => .app q (.ident q "$choice") as false
  (h ++ [.decl q c none false choice], .set p l' op (withOld q o? (.ident q c)))

/-- The clauses, with each choice the value of a binding: a clause that is a
    choice gets a name of its own, and `set L = a | b` and `var X:t = a | b`
    bind the choice first. -/
def normClauses (cs : List SExpr) : List SExpr :=
  cs.flatMap fun c =>
    let nm (p : Pos) : String := s!"$c{p.line}_{p.col}"
    match c with
    | .app p (.ident _ "$choice") _ false => [.decl p (nm p) none false c]
    | .set p l op rhs => match alts? rhs with
      | some as => let (h, s) := setClauses p l op as p; h ++ [s]
      | none => [c]
    | .decl p x ty true rhs =>
      if isChoice rhs then [.decl p (nm p) ty false rhs, .decl p x ty true (.ident p (nm p))] else [c]
    -- (`set L = a | b` as the last clause of a macro, which names its value)
    | .decl p x ty false (.set q l op rhs) => match alts? rhs with
      | some as => let (h, s) := setClauses q l op as q; h ++ [.decl p x ty false s]
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
access, `?`, tuples, arrays, maps and string interpolation. A choice
elsewhere (in a block, a branch, a struct construction, whose fields are
evaluated in declaration order, a named argument, or an alternative) is not
lifted, and the elaborator refuses it. -/

/-- The variable a `set` path starts from. -/
partial def rootName? : SExpr → Option String
  | .ident _ n => some n
  | .member _ e _ | .app _ e _ true => rootName? e
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
def headOps (isVal : String → Bool) (isField : String → String → Bool) : SExpr → List SExpr
  | f@(.ident _ n) => if isVal n then [f] else []
  -- (a field holding an array, map or function is read whole, first; a
  -- method's receiver only)
  | f@(.member _ (.ident _ n) m) => if isField n m then [f] else if isVal n then [recvOf f] else []
  | f@(.member _ _ _) => [recvOf f]
  | f => [f]


/-- Whether a call's head has a choice that lifting reaches. -/
partial def headHas (hasL : SExpr → Bool) : SExpr → Bool
  | .ident .. => false
  | .member _ obj _ => hasL obj
  | f => hasL f

/-- Whether `e` has a choice that lifting reaches. -/
partial def hasLiftable : SExpr → Bool
  | .app _ (.ident _ "$choice") _ false => true
  | .app _ f args _ => headHas hasLiftable f || args.any fun a =>
      (match a with | .decl _ n _ _ _ => !n.startsWith "?" | _ => true) && hasLiftable a
  | .bin _ _ a b => hasLiftable a || hasLiftable b
  | .cmp _ a rest => hasLiftable a || rest.any (hasLiftable ·.2)
  | .member _ e _ | .query _ e | .neg _ e => hasLiftable e
  | .tuple _ es | .arrayLit _ es => es.any hasLiftable
  | .str _ ps => ps.any fun | .code c => hasLiftable c | .text _ => false
  | .mapLit _ kvs => kvs.any fun (k, v) => hasLiftable k || hasLiftable v
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
  | .arrayLit _ [] | .mapLit _ [] => true
  | .ident _ n => !isVal n
  | .member _ (.ident _ n) _ => !isVal n
  | _ => false

structure LiftSt where
  next : Nat := 0
  /-- The clauses lifted so far, in order. -/
  pre : Array SExpr := #[]

abbrev LM := StateM LiftSt

def LM.fresh (p : Pos) (k : String) : LM String :=
  modifyGet fun s => (s!"${k}{p.line}_{p.col}_{s.next}", { s with next := s.next + 1 })

def LM.bind (p : Pos) (k : String) (e : SExpr) : LM SExpr := do
  let x ← LM.fresh p k
  modify fun s => { s with pre := s.pre.push (.decl p x none false e) }
  return .ident p x

mutual
/-- `e` with its liftable choices lifted (into the state's clauses). -/
partial def liftE (isVal : String → Bool) (isField : String → String → Bool) (e : SExpr) : LM SExpr := do
  if !hasLiftable e then return e
  match e with
  | .app p (.ident _ "$choice") _ false => LM.bind p "c" e
  | .app p f args br =>
    let hs := headOps isVal isField f
    let whole := match f, hs with
      | .member .., [h] => match h with | .member .. => true | _ => false
      | _, _ => true
    let ops := hs ++ args
    -- (named arguments are evaluated after the positional ones: one before
    -- the last choice would change places, so then no lifting)
    let last := (ops.zipIdx.filter (hasLiftable ·.1)).getLast?.map (·.2)
    let named := ops.zipIdx.any fun (a, i) => (match a with
      | .decl _ n _ _ _ => n.startsWith "?" | _ => false) && last.any (i < ·)
    if named then return e
    let ops' ← liftOps isVal isField ops
    let hs' := ops'.take hs.length
    let args' := ops'.drop hs.length
    let f' := match f, hs' with
      | .member q _ m, [o] => if whole then o else .member q o m
      | _, [h] => h
      | _, _ => f
    return .app p f' args' br
  | .bin p o a b => match ← liftOps isVal isField [a, b] with
    | [a', b'] => return .bin p o a' b'
    | _ => return e
  | .cmp p a rest => match ← liftOps isVal isField (a :: rest.map (·.2)) with
    | a' :: bs => return .cmp p a' ((rest.map (·.1)).zip bs)
    | [] => return e
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
  | e => return e

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
end

/-- A clause with the liftable choices inside it lifted: the clauses before
    it, then it. A binding or `set` whose value is a choice, or a clause that
    is one, stays as it is (`normClauses` makes it a binding). -/
def liftClause (isVal : String → Bool) (isField : String → String → Bool) (c : SExpr) : List SExpr :=
  let run (k : LM SExpr) : List SExpr :=
    let (c', st) := k.run {}
    st.pre.toList ++ [c']
  match c with
  | .app _ (.ident _ "$choice") _ false => [c]
  | .decl p x ty v rhs =>
    if isChoice rhs || !hasLiftable rhs then [c] else run do
      return .decl p x ty v (← liftE isVal isField rhs)
  | .set p l op rhs =>
    if isChoice rhs || !hasLiftable rhs then [c] else
      -- (the path's indices, then for `op=` the old value, then the
      -- lifted code, as `set` evaluates)
      let (h, o?, l') := setPrefix p l op
      h ++ run do return .set p l' op (withOld p o? (← liftE isVal isField rhs))
  | .gen p x i src =>
    if !hasLiftable src then [c] else run do return .gen p x i (← liftE isVal isField src)
  | e => if !hasLiftable e then [c] else run (liftE isVal isField e)

/-- The clauses ready for compiling: choices inside expressions lifted, and
    each choice the value of a binding. `isVal` says which names are values
    (variables and fields in scope); the clauses' own bindings are too. -/
def prepare (cs : List SExpr) (isVal : String → Bool := fun _ => false)
    (isField : String → String → Bool := fun _ _ => false) : List SExpr :=
  let bound := boundIn cs
  normClauses (cs.flatMap (liftClause (fun n => isVal n || bound.contains n) isField))

/-- Whether the clauses have a choice for their failure context to take. -/
def hasChoice (cs : List SExpr) : Bool := (prepare cs).any fun c => (binding? c).isSome

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
def takeFirst? : SExpr → Option SExpr
  | .block p cs => if hasChoice cs then some (firstOfClauses p cs) else none
  | e => if hasLiftable e then some (firstOfClauses e.pos [e]) else none

end OpenVerse.Front.Choice
