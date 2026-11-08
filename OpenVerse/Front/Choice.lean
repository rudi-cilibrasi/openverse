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

/-- Whether the clauses have a choice for their failure context to take. -/
def hasChoice (cs : List SExpr) : Bool := (normClauses cs).any fun c => (binding? c).isSome

end OpenVerse.Front.Choice
