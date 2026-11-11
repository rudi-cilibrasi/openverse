/- Generated for loops preserve the break target and condition writes. -/
import OpenVerse.Front.Suspend
import OpenVerse.Core.Interp

open OpenVerse OpenVerse.Front

private def int (n : Int) : Expr := .lit (.int n)
private def demand (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

private def frameContracts : IO Unit := do
  let fld (j : Nat) : Option Nat := if j == 2 then some 0 else none
  let st : St := {
    fr := [.ref 0, .void, .int 0],
    g := { out := [], heap := #[{ tag := 0, fields := [.int 0] }] } }
  let cases : List (String × Expr × Int) := [
    ("condition break commits its latest slot", .loop (.ite (.seq (.assign 2 (int 9)) .brk) (int 1) (int 2)), 9),
    ("condition failure rolls back", .loop (.ite (.seq (.assign 2 (int 9)) (.prim .fail [])) .brk .brk), 0),
    ("a local loop break stays transactional", .loop (.ite
      (.seq (.loop (.seq (.assign 2 (int 9)) .brk)) (.prim .fail [])) .brk .brk), 0),
    ("a successful condition commits after a local break", .loop (.ite
      (.loop (.seq (.assign 2 (int 9)) .brk)) .brk .brk), 9)]
  for (name, expr, expected) in cases do
    let rewritten := Suspend.toFields fld expr
    match eval { fns := [], main := 0 } 2000 st rewritten with
    | some (.ok _, state) =>
      demand name (state.g.heap[0]?.any (·.fields == [.int expected]))
    | other => throw (IO.userError s!"{name}: {repr other}")

private def env : Suspend.Env := {
  S := { fns := [], classes := [[.int]], protos := [(0, [])] }, ρ := .void,
  callee := fun _ => none, syncMark := 0, raceMark := 0, rushMark := 0,
  arity := 0, sites := 0, armsTotal := 0, fnBase := 0, schedTag := 0,
  nilTag := 0, resCellTag := 0, spawnMark := 0, spawns := #[],
  branchMark := 0, branches := #[], pcFld := 0, rS := 0, regionTotal := 0 }

private def variants : List Expr :=
  let stop := Expr.seq .brk (int 1)
  let fail := Expr.seq (.prim .fail []) (int 1)
  let say := Expr.print (.lit (Value.ofString "effect"))
  let bases := [int 1, fail, stop, .seq (.assign 2 (int 5)) stop,
    .seq (.loop .brk) (int 2), .assign 2 (.prim .add [.local 2, int 1]),
    .seq say (int 1), .seq say stop, .seq say fail, .heap (.set 0) [.local 0, int 7]]
  bases ++ bases.map (fun e => .ite (.seq (.assign 2 (int 3)) (.prim .fail [])) (int 4) e) ++
    bases.map (fun e => .seq (.assign 2 (.prim .add [.local 2, int 2])) e)

private def loopContracts : IO Unit := do
  let Γ := #[VTy.ref [0] [], .arr (.ref [0] []), .int, .arr .int]
  let initial : List Value := [.ref 0, .ofArray #[.ref 0, .ref 0], .int 0, .ofArray #[]]
  let mut count := 0
  for filter in variants do
    for body in variants do
      for used in [false, true] do
        let fe := Expr.forE 0 (.local 1) filter body
        let statement := if used then Expr.assign 3 fe else fe
        let original := Expr.seq (.loop (.seq statement .brk))
          (.prim .mkTup [.local 2, .local 3])
        let .ok (lowered, state) := ((Suspend.loopify original).run env).run { Γ }
          | throw (IO.userError "loop conversion failed")
        let fr := initial ++ ((state.Γ.toList.drop Γ.size).map VTy.default)
        let st : St := { fr, g := { out := [], heap := #[{ tag := 0, fields := [.int 0] }] } }
        let p : Prog := { fns := [], main := 0 }
        let before := eval p 10000 st original
        let after := eval p 10000 st lowered
        demand s!"loop conversion changed behavior: {repr original}\n{repr before}\n{repr after}"
          (match before, after with
          | some (r, s), some (r', s') => reprStr r == reprStr r' &&
              s.fr[2]? == s'.fr[2]? && s.fr[3]? == s'.fr[3]? && reprStr s.g == reprStr s'.g
          | _, _ => false)
        count := count + 1
  IO.println s!"suspension break contracts: {count} loop cases and 4 frame cases passed"

def main : IO Unit := do
  frameContracts
  loopContracts
