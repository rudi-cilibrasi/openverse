/-
  OpenVerse front end — built-in functions as values.

  A built-in function is a function like any other (the Book's tests pass
  `Sin` to a parameter `F(:float):float`). Where a program names one as a
  value, not as the head of a call, and neither defines that name nor binds
  it, the program gets an ordinary definition of it, whose body calls the
  built-in by its hidden name `$F` and whose effects are the built-in's;
  `FnValues` then makes it a value as it makes any function one, and the
  program's calls of `F` call it. Only the built-ins of one signature have
  such a definition (`signatures`): an overloaded or generic one (`Abs` of
  an int or a float, `ToString`, `Concatenate`) is no value, as an
  overloaded function is not (the elaborator says so).
-/
import OpenVerse.Front.Syntax

namespace OpenVerse.Front.BuiltinValues

/-- The built-ins of one signature: name, parameter types, effects, result
    type (the Book's Runtime API, "Math"; #132, #490). They are the soft
    built-ins, which a program may also define; `Quotient` and `Mod`, of one
    signature too, are names a program may not define, so they have no
    such definition. -/
def signatures : List (String × List String × List String × String) :=
  let unary (fx : List String) (n : String) := (n, ["float"], fx, "float")
  ["Sqrt", "Exp", "Ln", "Sin", "Cos", "Tan", "ArcSin", "ArcCos"].map (unary ["computes"]) ++
  ["Sinh", "Cosh", "Tanh", "ArSinh", "ArCosh", "ArTanh"].map (unary ["reads"]) ++
  [("Pow", ["float", "float"], ["computes"], "float"), ("Log", ["float", "float"], ["computes"], "float"),
   ("Lerp", ["float", "float", "float"], ["reads"], "float"),
   ("IsFinite", ["float"], ["computes", "decides"], "float"),
   ("Round", ["float"], ["computes", "decides"], "int"), ("Int", ["float"], ["computes", "decides"], "int")]

/-- The names an expression uses as values (not as the head of a call), with
    where, and the names it binds. -/
partial def scan : SExpr → List (Pos × String) × List String
  | .ident p n => ([(p, n)], [])
  | .app _ (.ident _ _) as _ => scanAll as
  | e =>
    let (uses, binds) := scanAll e.children
    match e with
    | .decl _ n _ _ _ => (uses, n :: binds)
    | .gen _ n i _ => (uses, n :: i.toList ++ binds)
    | _ => (uses, binds)
where
  scanAll (es : List SExpr) : List (Pos × String) × List String :=
    es.foldl (fun (u, b) e => let (u', b') := scan e; (u ++ u', b ++ b')) ([], [])

/-- `scan` over a definition: its bodies, defaults and parameters. -/
partial def scanTop : STop → List (Pos × String) × List String
  | .fn _ n ps _ _ _ b =>
    let (u, bs) := scan.scanAll (b :: ps.filterMap (·.default))
    (u, n :: ps.map (·.name) ++ bs)
  | .const _ n _ e => let (u, bs) := scan e; (u, n :: bs)
  | .classDef _ n _ _ _ _ fs _ ms =>
    let (u, bs) := scan.scanAll (fs.filterMap (·.2.2.1))
    let inner := ms.map scanTop
    (u ++ inner.flatMap (·.1), n :: fs.map (·.1) ++ bs ++ inner.flatMap (·.2))

/-- The definitions of the built-ins `tops` names as values and neither
    defines nor binds. -/
def wrappers (tops : List STop) : List STop :=
  let scans := tops.map scanTop
  let uses := scans.flatMap (·.1)
  let bound := scans.flatMap (·.2)
  let taken (n : String) := bound.any fun b => b == n || b.endsWith ("::" ++ n)
  signatures.filterMap fun (n, ps, fx, r) =>
    match uses.find? (·.2 == n) with
    | some (p, _) =>
      if taken n then none else
      let params := ps.zipIdx.map fun (t, i) => ({ name := s!"X{i}", ty := .name t } : SParam)
      let call := SExpr.app p (.ident p ("$" ++ n)) (params.map (.ident p ·.name)) (fx.contains "decides")
      some (.fn p n params [] fx (.name r) call)
    | none => none

end OpenVerse.Front.BuiltinValues
