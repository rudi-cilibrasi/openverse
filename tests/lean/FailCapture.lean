/- Failure outcomes must preserve effects without changing transactions. -/
import OpenVerse.Front.FailCapture
import OpenVerse.Core.Check
import OpenVerse.Core.Control
import OpenVerse.Core.Interp

open OpenVerse OpenVerse.Front

private def int (n : Int) : Expr := .lit (.int n)
private def fail : Expr := .prim .fail []
private def say (s : String) : Expr := .print (.lit (Value.ofString s))
private def write (n : Int) : Expr := .heap (.set 0) [.local 0, int n]
private def count : Expr := .heap (.get 0) [.local 0]
private def packet (v : Expr) : Expr := .prim .mkTup [v, count]

private def demand (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

private def lowered (fns : Array Fn) (slots : Array (List VTy)) (sigs : Sigs) :
    IO (Prog × Sigs × Array (List VTy)) := do
  match FailCapture.lower fns slots sigs with
  | .error e => throw (IO.userError e)
  | .ok (fs, gs, ss) =>
    let p : Prog := { fns := fs.toList, main := 1 }
    demand "lowered program checks" p.check
    demand "lowered control checks" p.checkControl
    for i in List.range fs.size do
      let (ps, t) := ss.fns[i]!
      demand s!"lowered function {fs[i]!.name} types: {repr gs[i]!} {repr fs[i]!.body}"
        (checkFn ss fs[i]! ps t gs[i]!)
    demand "whole-program types check" (p.checkTypes ss gs.toList)
    return (p, ss, gs)

private def dispatchCheck (fails : Bool) : IO Unit := do
  let a := VTy.var 0
  let base := VTy.ref [0, 1] [a]
  let counter := VTy.ref [2] []
  let packet (v : Expr) := Expr.prim .mkTup
    [v, .heap (.get 0) [.local 2], .heap .tag [.local 4]]
  let argument := Expr.seq (.assign 4 (.local 1)) (.call 3 [.local 2])
  let body := Expr.ite (.heap (.isTag [1]) [.local 4]) (.call 2 [.local 4, argument]) fail
  let owner : Fn := {
    name := "dispatch", arity := 3, nslots := 6, decides := true,
    body := initPrefixE 3 [.lit .none, .local 0, .lit .none]
      (.seq (.assign 5 (.prim .mkSome [FailCapture.marked 3 body (.ret (packet (.lit .none)))]))
        (packet (.local 5))) }
  let driver : Fn := {
    name := "Main", arity := 0, nslots := 0, decides := true,
    body := .call 0 [.heap (.new 1) [int 10], .heap (.new 0) [int 20], .heap (.new 2) [int 0]] }
  let method : Fn := {
    name := "method", arity := 2, nslots := 2, decides := false,
    body := .prim .add [.heap (.get 0) [.local 0], .local 1] }
  let argumentFn : Fn := {
    name := "argument", arity := 1, nslots := 1, decides := true,
    body := .seq (write 9) (.seq (say "arg") (if fails then fail else int 5)) }
  let result := VTy.tup [.opt a, .int, .int]
  let sigs : Sigs := {
    fns := [([base, base, counter], result), ([], result.subst (fun _ => .int)),
      ([.ref [1] [.int], .int], .int), ([counter], .int)],
    classes := [[a], [a], [.int]], pins := [[], [some .int], []] }
  let slots := #[[base, base, counter, .opt a, base, .opt a], [], [.ref [1] [.int], .int], [counter]]
  let (p, _, _) ← lowered #[owner, driver, method, argumentFn] slots sigs
  let want : Value := .tup [if fails then .none else .some (.int 15), .int 9, .int 0]
  match p.run 20000 with
  | some (.ok got, printed) =>
    demand s!"dispatch receiver snapshot (fails={fails}): {repr got} {repr printed}"
      (got == want && printed == "arg\n".toList.map (·.toNat))
  | other => throw (IO.userError s!"dispatch: {repr other}")

/-- Slot 0 is a shared counter, 1 the result-type witness, and 2 the
    successful result. A failing body returns the current counter too. -/
private def check (name : String) (body : Expr) (ty : VTy) (value : Value)
    (out : String := "") (extra : Array Fn := #[])
    (extraSigs : List (List VTy × VTy) := []) (extraSlots : Array (List VTy) := #[])
    (error : Bool := false) : IO Unit := do
  let owner : Fn := {
    name := name, arity := 1, nslots := 3, decides := true,
    body := initPrefixE 1 [.lit .none, .lit .none]
      (.seq (.assign 2 (.prim .mkSome [FailCapture.marked 1 body (.ret (packet (.lit .none)))]))
        (packet (.local 2))) }
  let driver : Fn := {
    name := "Main", arity := 0, nslots := 0, decides := true,
    body := .call 0 [.heap (.new 0) [int 0]] }
  let counter := VTy.ref [0] []
  let ret := VTy.tup [.opt ty, .int]
  let sigs : Sigs := {
    fns := ([counter], ret) :: ([], ret) :: extraSigs, classes := [[.int]] }
  let slots := #[[counter, .opt ty, .opt ty], []] ++ extraSlots
  let (p, _, _) ← lowered (#[owner, driver] ++ extra) slots sigs
  match p.run 20000 with
  | some (.ok got, printed) =>
    demand s!"{name}: got {repr got}, output {repr printed}"
      (!error && got == value && printed == out.toList.map (·.toNat))
  | some (.err .user, printed) =>
    demand name (error && printed == out.toList.map (·.toNat))
  | other => throw (IO.userError s!"{name}: {repr other}")

def main : IO Unit := do
  let no (n : Int) : Value := .tup [.none, .int n]
  let yes (v : Value) (n : Int) : Value := .tup [.some v, .int n]
  let effect (n : Int) (s : String) (e : Expr) := Expr.seq (write n) (.seq (say s) e)
  check "direct failure" (effect 9 "body" fail) .int (no 9) "body\n"
  check "successful body" (effect 9 "body" (int 5)) .int (yes (.int 5) 9) "body\n"
  check "failed condition rolls back" (.ite (effect 9 "lost" fail) (int 1) (int 5))
    .int (yes (.int 5) 0)
  check "failed then retains condition" (.ite (say "cond") (effect 9 "body" fail) (int 5))
    .int (no 9) "cond\nbody\n"
  check "failed operation keeps argument effects"
    (.prim .index [.lit (.ofArray #[.int 1]), effect 9 "index" (int 7)])
    .int (no 9) "index\n"
  -- Reserve the loop element as an extra parameter of a callee so the
  -- owner's result-type witnesses cannot be rebound by the generator.
  let counter := VTy.ref [0] []
  let loopFn (filter body : Expr) : Fn := {
    name := "loop", arity := 1, nslots := 2, decides := true,
    body := initPrefixE 1 [int 0] (.forE 1 (.prim .mkArr [int 1, int 2]) filter body) }
  check "filter rollback" (.call 2 [.local 0]) (.arr .int) (yes (.ofArray #[]) 0)
    "" #[loopFn (effect 7 "lost" fail) (int 5)] [([counter], .arr .int)] #[[counter, .int]]
  check "body failure stops loop" (.call 2 [.local 0]) (.arr .int) (no 9)
    "filter\nbody\n" #[loopFn (effect 7 "filter" (.lit .void)) (effect 9 "body" fail)]
    [([counter], .arr .int)] #[[counter, .int]]
  let iterator : Fn := {
    name := "iterator", arity := 1, nslots := 2, decides := true,
    body := initPrefixE 1 [int 0] (.forE 1 (effect 9 "iterator" fail) (.lit .void) (int 5)) }
  check "failed iterator keeps effects" (.call 2 [.local 0]) (.arr .int) (no 9)
    "iterator\n" #[iterator] [([counter], .arr .int)] #[[counter, .int]]
  let callee : Fn := {
    name := "callee", arity := 1, nslots := 1, decides := true,
    body := effect 9 "callee" fail }
  check "callee failure keeps effects" (.call 2 [.local 0]) .int (no 9)
    "callee\n" #[callee] [([counter], .int)] #[[counter]]
  let recursive : Fn := {
    name := "recursive", arity := 2, nslots := 2, decides := true,
    body := .seq (say "r") (.ite (.prim .gt [.local 1, int 0])
      (.call 2 [.local 0, .prim .sub [.local 1, int 1]]) fail) }
  check "recursive outcomes" (.call 2 [.local 0, int 2]) .int (no 0)
    "r\nr\nr\n" #[recursive] [([counter, .int], .int)] #[[counter, .int]]
  check "runtime errors stay errors" (effect 9 "error" (.prim .userErr [])) .int .void
    "error\n" (error := true)
  let returns : Fn := {
    name := "returns", arity := 1, nslots := 1, decides := true,
    body := .ite (.seq (say "return") (.ret (int 7))) fail fail }
  check "return in an existing condition" (.call 2 [.local 0]) .int (yes (.int 7) 0)
    "return\n" #[returns] [([counter], .int)] #[[counter]]
  let breaking : Fn := {
    name := "breaking", arity := 1, nslots := 1, decides := true,
    body := .seq (.loop (.ite (.seq (say "break") .brk) fail fail)) (int 7) }
  check "break keeps its original loop" (.call 2 [.local 0]) .int (yes (.int 7) 0)
    "break\n" #[breaking] [([counter], .int)] #[[counter]]
  dispatchCheck true
  dispatchCheck false
  let untouched : Array Fn := #[{
    name := "plain", arity := 0, nslots := 0,
    decides := false, body := int 3 }]
  let .ok (fs, gs, _) := FailCapture.lower untouched #[[]] { fns := [([], .int)] }
    | throw (IO.userError "unmarked lowering failed")
  demand "unmarked functions stay identical" (reprStr fs == reprStr untouched && gs == #[[]])
  IO.println "failure-capture contracts passed"
