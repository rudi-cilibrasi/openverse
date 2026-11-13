import OpenVerse.Front.Elab

open OpenVerse.Front

/-!
(#283) A method with several values whose family is selected stays in its class as a stub
(`Choice.familyStub`), whose body is `Err()`, for the elaborator's checks of members and
overrides; every call of the method is rewritten into a call of the family's functions.
`elabProgramCore` gives out no program in which a function calls a stub, whatever made the
call. No source reaches that today, so these contracts make one: a use's family, noted by its
place for the next round (`Requests.families`), names a root that is none of the method's, so
the use stays as written, an ordinary call of the stub, which must be refused; with the root
an elaboration notes, the same program compiles.
-/

def source : String :=
  "a := class:\n    M()<transacts>:int = 1 | 2\nb := class:\n    M()<transacts>:int = 30 | 40\n" ++
  "Main()<transacts>:void =\n    for (X := a{}.M()) { Print(\"x {X}\") }\n"

def main : IO Unit := do
  let tops ← match parseProgram source with
    | .ok tops => pure tops
    | .error e => throw (IO.userError s!"parse: {e}")
  -- (the use `a{}.M` is at 6:17)
  let use : Pos := { line := 6, col := 17 }
  match elabProgram tops { requests := { families := [(use, "nowhere")] } } with
  | .ok _ => throw (IO.userError "a program calling a family's stub was given out")
  | .error e =>
    if (e.splitOn "2:4: a.M has several values, but a call of it in Main is compiled as one of a method of one value").length ≤ 1 then
      throw (IO.userError s!"unexpected diagnostic for a call of a stub: {e}")
  match elabProgram tops { requests := { families := [(use, "a")] } } with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"the family's call was refused: {e}")
  match elabProgram tops with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"the program was refused: {e}")
  IO.println "family stub contracts passed"
