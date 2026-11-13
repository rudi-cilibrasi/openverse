/- Elaboration of a program's source, before its classes and types (phases 1–3 of
   `elabProgramCore`); public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Lowering

namespace OpenVerse.Front
open OpenVerse

/-- A program's definitions complete (`argsAndMethodOverloads`), as the class
    phases start from them. -/
structure Definitions where
  /-- The definitions, `Args` and the entry expression's `$Do` included, each
      overloaded method renamed by its parameter list (`M$ovN`, #106). -/
  tops : List STop
  /-- The overloaded methods' parameter lists (`MethodOverloads`). -/
  methodOverloads : MethodOverloads

/-- `Args` and method overloads, a phase of `elabProgramCore`: the definitions
    `tops`, then `Args`, bound to the command line's arguments `args` (unless
    the program defines `Args`), then the entry expression's function `entry`;
    each method name declared with two or more parameter lists renamed by its
    list (#106). -/
def argsAndMethodOverloads (tops entry : List STop) (args : Option (List String)) :
    Except String Definitions := do
  -- the command line: `Args`, and an entry expression
  let defines (n : String) := tops.any fun
    | .fn _ m .. | .const _ m .. | .classDef _ m .. => m == n
  let argsTop : List STop :=
    match args with
    | some as =>
      if defines "Args" then []
      else [.const { line := 0, col := 0 } "Args" (some (.arr (.name "string")))
              (.arrayLit { line := 0, col := 0 } (as.map fun a => .str { line := 0, col := 0 } [.text a]))]
    | none => []
  -- overloaded methods (#106): a method name declared with two or more
  -- parameter lists is renamed, in every class and interface, by its list
  -- (`M$ovN`, `MethodOverloads`): an override has its method's list, so its
  -- name too
  let mo := MethodOverloads.of (tops ++ argsTop ++ entry)
  let allTops0 ← mo.apply (tops ++ argsTop ++ entry)
  return { tops := allTops0, methodOverloads := mo }

end OpenVerse.Front
