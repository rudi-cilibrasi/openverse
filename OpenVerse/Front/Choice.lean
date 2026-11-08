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

/-- A binding of a choice, the form the elaborator compiles: its position,
    name, written type and alternatives. -/
def binding? : SExpr → Option (Pos × String × Option STy × List SExpr)
  | .decl p x ty false rhs => (alts? rhs).map fun as => (p, x, ty, as)
  | _ => none

/-- The clauses, with each choice the value of a binding: a clause that is a
    choice gets a name of its own, and `set L = a | b` and `var X:t = a | b`
    bind the choice first. -/
def normClauses (cs : List SExpr) : List SExpr :=
  cs.flatMap fun c =>
    let nm (p : Pos) : String := s!"$c{p.line}_{p.col}"
    match c with
    | .app p (.ident _ "$choice") _ false => [.decl p (nm p) none false c]
    | .set p l op rhs =>
      if isChoice rhs then [.decl p (nm p) none false rhs, .set p l op (.ident p (nm p))] else [c]
    | .decl p x ty true rhs =>
      if isChoice rhs then [.decl p (nm p) ty false rhs, .decl p x ty true (.ident p (nm p))] else [c]
    | c => [c]

/-- Whether the clauses have a choice for their failure context to take. -/
def hasChoice (cs : List SExpr) : Bool := (normClauses cs).any fun c => (binding? c).isSome

end OpenVerse.Front.Choice
