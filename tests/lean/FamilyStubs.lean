import OpenVerse.Front.Elab
import OpenVerse.Core.Interp

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
  -- A continuation may discover an overload after its site was previously
  -- unreachable. Retire the empty sentinel and execute the real template,
  -- rather than the single-value checking stub (#653, modeled seed 653109).
  let orderSource := String.intercalate "\n" [
    "Dup(V:t where t:type):t=V|V",
    "Ov(N:int)<transacts>:int=N+1|N*2",
    "Ov(N:int,M:int)<transacts>:int=N-M|M*3",
    "Take(N:int):int=",
    "    Y:=N|N+1",
    "    Print(\"p{Y}\")",
    "    if(Y=N+1):return 99|98",
    "    Y",
    "Main():void=",
    "    if(A:=Dup(0)|Dup(1),B:=Take(Ov(-1))):Print(\"value {B}\")"]
  let expected := "p0\nvalue 0\n".toList.map Char.toNat
  for requests in ([{}, { overloads := [({ line := 10, col := 34 }, "")] }] : List Requests) do
    let compiled ← match compileChecked orderSource { requests } with
      | .ok c => pure c
      | .error e => throw (IO.userError s!"copied overload continuation: {e}")
    match compiled.prog.run 100000 with
    | some (.ok _, out) =>
      unless out == expected do throw (IO.userError s!"a copied overload continuation executed its checking stub: {out}")
    | result => throw (IO.userError s!"copied overload continuation did not succeed: {reprStr result}")
  IO.println "family stub contracts passed"
