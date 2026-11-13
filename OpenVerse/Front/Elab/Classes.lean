/- Elaboration of a program's classes and interfaces (phases 4–6 of `elabProgramCore`);
   public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Lowering

namespace OpenVerse.Front
open OpenVerse

/-- The fields of the classes and interfaces. -/
structure Fields where
  /-- Each class's fields, by its name: its superclass's, then those of the
      interfaces above it that are not there yet, then its own, then hidden
      ones that hold values of its type parameters (#209); each with its
      type, its default and whether it is a `var`. -/
  map : Std.HashMap String (List (String × STy × Option SExpr × Bool))
  /-- The inherited fields a class gives again (`<override>`, or reached through
      two parents), with the type it gives them: `checkSignatures` checks, once
      types are resolved, that it is the inherited one. -/
  overrides : Array (Pos × String × String × STy)
  /-- A refusal for each field that two interfaces give defaults, which
      `checkSignatures` gives after the signature checks. -/
  defaultClashes : Array String

/-- The classes' methods and constructors, as functions. -/
structure Methods where
  /-- The program's definitions with each class expanded: a struct of its
      fields, and each method `M` a function `c.M` whose first parameter is
      `Self`; and each constructor its functions (`expandCtors`). -/
  tops : List STop
  /-- The methods that are a family's stub (`Choice.familyStub`), as functions,
      each where it is declared. -/
  stubs : List (String × Pos)
  /-- The abstract methods, each with its class. -/
  abstracts : Array (String × String)
  /-- Each override where it is, as `c.M`, with the method `q.M` it overrides. -/
  overridePairs : Array (Pos × String × String)
  /-- Each implementation `e.M` a concrete class `c` uses for a declaration
      `q.M` above it, with `c`'s position: `checkSignatures` checks they agree. -/
  implChecks : Array (Pos × String × String × String)

end OpenVerse.Front
