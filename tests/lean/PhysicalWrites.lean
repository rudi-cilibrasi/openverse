import OpenVerse.Front.PhysicalWrites
import OpenVerse.Core.Check
import OpenVerse.Core.Control
import OpenVerse.Core.TypeCheck
import OpenVerse.Core.Bounded

open OpenVerse OpenVerse.Front

private def checkSmall : IO Unit := do
  let make (name : String) (arity slots : Nat) (body : Expr) (writes := false) : Fn :=
    { name, arity, nslots := slots, body, writes, decides := false }
  let input := #[
    make "Main" 0 0 (.call 1 []),
    make "Outer" 0 0 (.call 2 []),
    make "Inner" 0 0 (.call 3 [.heap (.new 0) [.lit (.int 0)]]),
    make "Store" 1 1 (.heap (.set 0) [.local 0, .lit (.int 7)]),
    make "Declared" 0 0 (.lit (.int 0)) true,
    make "DeclaredCaller" 0 0 (.call 4 []),
    make "CycleA" 1 1 (.call 7 [.local 0]),
    make "CycleB" 1 1 (.seq (.heap (.set 0) [.local 0, .lit (.int 1)]) (.call 6 [.local 0])),
    make "Local" 0 1 (.seq (.assign 0 (.lit (.int 2))) (.local 0)),
    make "Allocate" 0 0 (.heap (.new 0) [.lit (.int 0)])]
  let before : Prog := { fns := input.toList, main := 0 }
  unless !before.checkWriteSound do throw <| IO.userError "control must expose missing physical flags"
  let output := PhysicalWrites.annotate input
  unless output.toList.map (·.writes) == [true,true,true,true,true,true,true,true,false,false] do
    throw <| IO.userError "incorrect physical write closure"
  unless (PhysicalWrites.annotate output).toList.map (·.writes) == output.toList.map (·.writes) do
    throw <| IO.userError "physical annotation must be idempotent"
  let code (functions : Array Fn) := functions.toList.map fun fn => reprStr { fn with writes := false }
  unless code output == code input do
    throw <| IO.userError "physical annotation changed code or calling conventions"
  let prog : Prog := { fns := output.toList, main := 0 }
  let box : VTy := .ref [0] []
  let sigs : Sigs := {
    fns := [([], .int),([], .int),([], .int),([box], .int),([], .int),([], .int),
      ([box], .int),([box], .int),([], .int),([], box)], classes := [[.int]], pins := [[]] }
  let slots := [[],[],[],[box],[],[],[box],[box],[.int],[]]
  unless prog.check && prog.checkControl && prog.checkTypes sigs slots do
    throw <| IO.userError "truthful physical annotation must retain all Core checks"
  match prog.runB 1000 1000 with
  | .res (.ok (.int 7), []) => pure ()
  | _ => throw <| IO.userError "physical annotation changed execution"
  let invalid : Fn := make "Invalid" 0 0 (.call 1000 [])
  let invalid : Prog := { fns := (PhysicalWrites.annotate #[invalid]).toList, main := 0 }
  unless !invalid.check do throw <| IO.userError "write annotation must not admit an invalid call"
  IO.println "physical write annotation passed (callers, cycles, conservative declarations, locals, allocation, Core checks and execution)"

private def checkScale : IO Unit := do
  let count := 32000
  let functions := (List.range count).toArray.map fun index =>
    ({ name := s!"Reverse{index}", arity := 0, nslots := 0, decides := false,
       body := .call (index+1) [] } : Fn)
  let writer : Fn := {
    name := "Store", arity := 0, nslots := 0, decides := false
    body := .heap (.set 0) [.heap (.new 0) [.lit (.int 0)], .lit (.int 1)] }
  let functions := functions.push writer
  let started ← IO.monoMsNow
  let output := PhysicalWrites.annotate functions
  unless output.size == functions.size && output.all (·.writes) do
    throw <| IO.userError "reverse caller propagation missed a writer"
  IO.println s!"physical write annotation scaling passed (32000 reversed calls, {(← IO.monoMsNow)-started} ms)"

def main (args : List String) : IO Unit := do
  if args == ["--scale"] then checkScale else checkSmall
