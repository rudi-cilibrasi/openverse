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

/-- `set L op= a | b` with the choice bound first, as `set` evaluates (Book
    of Verse §3.5): the indices of `L`'s path, then (for `op=`) the old
    value, then the new one, so the alternatives come after them. -/
partial def setClauses (p : Pos) (l : SExpr) (op : Option String) (as : List SExpr) (q : Pos) :
    List SExpr × SExpr :=
  let nm (k : String) : String := s!"${k}{q.line}_{q.col}"
  -- (each index of the path, bound to a name in order, unless a literal)
  let rec hoist (n : Nat) : SExpr → List SExpr × SExpr × Nat
    | .app r base args true =>
      let (h, base', n) := hoist n base
      let (h2, args', n) := args.foldl (fun (h, acc, n) a => match a with
        | .int .. | .char .. | .char32 .. | .str _ [] => (h, acc ++ [a], n)
        | a => (h ++ [.decl r (nm s!"i{n}_") none false a], acc ++ [.ident r (nm s!"i{n}_")], n + 1)) (h, [], n)
      (h2, .app r base' args' true, n)
    | .member r base f =>
      let (h, base', n) := hoist n base
      (h, .member r base' f, n)
    | e => ([], e, n)
  let (h, l', _) := hoist 0 l
  let c := SExpr.ident q (nm "c")
  match op with
  | none => (h ++ [.decl q (nm "c") none false (.app q (.ident q "$choiceAt") (l' :: as) false)], .set p l' none c)
  | some o =>
    (h ++ [.decl q (nm "o") none false l', .decl q (nm "c") none false (.app q (.ident q "$choice") as false)],
      .set p l' none (.bin q o (.ident q (nm "o")) c))

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

/-- A call's head whose receiver is evaluated as an operand: `obj.M(…)`
    with `obj` not a name (a variable, module or class, which are not lifted). -/
def receiver? : SExpr → Option SExpr
  | .member _ obj _ => match obj with
    | .ident .. => none
    | o => some o
  | _ => none

/-- Whether `e` has a choice that lifting reaches. -/
partial def hasLiftable : SExpr → Bool
  | .app _ (.ident _ "$choice") _ false => true
  | .app _ f args _ => ((receiver? f).map hasLiftable).getD false || args.any fun a =>
      (match a with | .decl _ n _ _ _ => !n.startsWith "?" | _ => true) && hasLiftable a
  | .bin _ _ a b => hasLiftable a || hasLiftable b
  | .cmp _ a rest => hasLiftable a || rest.any (hasLiftable ·.2)
  | .member _ e _ | .query _ e | .neg _ e => hasLiftable e
  | .tuple _ es | .arrayLit _ es => es.any hasLiftable
  | .str _ ps => ps.any fun | .code c => hasLiftable c | .text _ => false
  | .mapLit _ kvs => kvs.any fun (k, v) => hasLiftable k || hasLiftable v
  | _ => false

/-- Literals, and names that the clause does not `set`: the same whenever
    they are evaluated, so not bound to a name of their own. -/
def stable (sets : List String) : SExpr → Bool
  | .int .. | .char .. | .char32 .. | .float .. => true
  | .ident _ n => !sets.contains n
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
partial def liftE (sets : List String) (e : SExpr) : LM SExpr := do
  if !hasLiftable e then return e
  match e with
  | .app p (.ident _ "$choice") _ false => LM.bind p "c" e
  | .app p f args br =>
    match receiver? f with
    | some obj =>
      match ← liftOps sets (obj :: args) with
      | obj' :: args' => match f with
        | .member q _ m => return .app p (.member q obj' m) args' br
        | _ => return .app p f args' br
      | [] => return e
    | none => return .app p f (← liftOps sets args) br
  | .bin p o a b => match ← liftOps sets [a, b] with
    | [a', b'] => return .bin p o a' b'
    | _ => return e
  | .cmp p a rest => match ← liftOps sets (a :: rest.map (·.2)) with
    | a' :: bs => return .cmp p a' ((rest.map (·.1)).zip bs)
    | [] => return e
  | .member p x m => return .member p (← liftE sets x) m
  | .query p x => return .query p (← liftE sets x)
  | .neg p x => return .neg p (← liftE sets x)
  | .tuple p es => return .tuple p (← liftOps sets es)
  | .arrayLit p es => return .arrayLit p (← liftOps sets es)
  | .str p ps =>
    let codes := ps.filterMap fun | .code c => some c | .text _ => none
    let codes' ← liftOps sets codes
    let rec put : List SPart → List SExpr → List SPart
      | .code _ :: ps, c :: cs => .code c :: put ps cs
      | p :: ps, cs => p :: put ps cs
      | [], _ => []
    return .str p (put ps codes')
  | .mapLit p kvs =>
    let flat ← liftOps sets (kvs.flatMap fun (k, v) => [k, v])
    let rec pairs : List SExpr → List (SExpr × SExpr)
      | k :: v :: r => (k, v) :: pairs r
      | _ => []
    return .mapLit p (pairs flat)
  | e => return e

/-- Operands evaluated left to right: the liftable choices of each are
    lifted, and every operand before the last one with such a choice is
    bound to a name first (unless `stable`), so it still runs before it. -/
partial def liftOps (sets : List String) (es : List SExpr) : LM (List SExpr) := do
  let last := (es.zipIdx.filter (hasLiftable ·.1)).getLast?.map (·.2)
  match last with
  | none => return es
  | some j =>
    let mut out := #[]
    for (e, i) in es.zipIdx do
      if i < j then
        let e' ← liftE sets e
        out := out.push (← if stable sets e' then pure e' else LM.bind e.pos "t" e')
      else if i == j then out := out.push (← liftE sets e)
      else out := out.push e
    return out.toList
end

/-- A clause with the liftable choices inside it lifted: the clauses before
    it, then it. A binding or `set` whose value is a choice, or a clause that
    is one, stays as it is (`normClauses` makes it a binding). -/
def liftClause (c : SExpr) : List SExpr :=
  let run (k : List String → LM SExpr) : List SExpr :=
    let (c', st) := (k (setsIn c)).run {}
    st.pre.toList ++ [c']
  match c with
  | .app _ (.ident _ "$choice") _ false => [c]
  | .decl p x ty v rhs =>
    if isChoice rhs || !hasLiftable rhs then [c] else run fun sets => do
      return .decl p x ty v (← liftE sets rhs)
  | .set p l op rhs =>
    -- (only into a plain variable, which is read, for `op=`, after the
    -- lifted clauses: so not when they write it)
    match l with
    | .ident _ n =>
      if isChoice rhs || !hasLiftable rhs || (op.isSome && (setsIn rhs).contains n) then [c]
      else run fun sets => do return .set p l op (← liftE sets rhs)
    | _ => [c]
  | .gen p x i src =>
    if !hasLiftable src then [c] else run fun sets => do return .gen p x i (← liftE sets src)
  | e => if !hasLiftable e then [c] else run fun sets => liftE sets e

/-- The clauses ready for compiling: choices inside expressions lifted, and
    each choice the value of a binding. -/
def prepare (cs : List SExpr) : List SExpr := normClauses (cs.flatMap liftClause)

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
