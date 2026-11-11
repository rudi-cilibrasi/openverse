/- Executable contracts for the shared storage used by refining lifts. -/
import OpenVerse.Front.FrameRefs
import OpenVerse.Core.Interp

open OpenVerse OpenVerse.Front

private def demand (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

private def rewritten (slots : Array VTy) (aliases : List FrameRefs.Slot)
    (copies : List FrameRefs.CopyOut) (e : Expr) : IO FrameRefs.Rewritten :=
  match FrameRefs.rewrite slots aliases copies e with
  | .ok r => pure r
  | .error e => throw (IO.userError e)

private def int (n : Int) : Expr := .lit (.int n)

private def initial : St :=
  { fr := [.ref 0, .int (-99), .tup [.int 2], .int 0],
    g := { out := [], heap := #[{ tag := 0, fields := [.int 1] }] } }

private def checkRun (name : String) (body : Expr) (value field : Int)
    (fns : List Fn := []) : IO Unit := do
  let got := eval { fns, main := 0 } 1000 initial body
  match got with
  | some (.ok (.int v), st) =>
    demand name (v == value && st.g.heap[0]?.any (·.fields == [.int field]))
  | _ => throw (IO.userError s!"{name}: {repr got}")

private def slots : Array VTy := #[.ref [0] [], .int, .tup [.int], .int]
private def aliases : List FrameRefs.Slot := [{ localSlot := 1, frame := 0, field := 0 }]

def main : IO Unit := do
  let r ← rewritten slots aliases [] (.assign 1 (int 7))
  checkRun "an assignment preserves its result" r.body 7 7

  let readFn : Fn := {
    name := "read", arity := 1, nslots := 1, decides := false,
    writes := false, body := .heap (.get 0) [.local 0] }
  let e := Expr.ite (.seq (.assign 1 (int 7)) (.call 0 [.local 0])) (.local 1) (int (-1))
  let r ← rewritten slots aliases [] e
  checkRun "a condition's later helper sees its writes" r.body 7 7 [readFn]

  let e := Expr.ite (.seq (.assign 1 (int 7)) (.prim .fail [])) (int (-1)) (.local 1)
  let r ← rewritten slots aliases [] e
  checkRun "a failed condition rolls the shared write back" r.body 1 1

  let writeFn : Fn := {
    name := "write", arity := 1, nslots := 1, decides := false,
    body := .heap (.set 0) [.local 0, int 9] }
  let r ← rewritten slots aliases [] (.seq (.call 0 [.local 0]) (.local 1))
  checkRun "an alias sees a callback's latest write" r.body 9 9 [writeFn]

  let copies : List FrameRefs.CopyOut := [{ target := 1, result := 2, field := some 0 }]
  let e := Expr.seq (.assign 1 (.prim (.tupGet 0) [.local 2])) (.local 1)
  let r ← rewritten slots aliases copies e
  checkRun "a saved tuple does not overwrite a later shared update" r.body 1 1

  let copies : List FrameRefs.CopyOut := [{ target := 1, result := 3 }]
  let e := Expr.seq (.assign 1 (.local 3)) (.local 1)
  let r ← rewritten slots aliases copies e
  checkRun "a scalar copy-out does not overwrite shared storage" r.body 1 1

  let e := Expr.seq (.assign 3 (.local 1)) (.seq (.call 0 [.local 0]) (.local 3))
  let r ← rewritten slots aliases [] e
  checkRun "a user copy or saved return operand remains a snapshot" r.body 1 9 [writeFn]

  let e := Expr.seq (.assign 1 (.local 3)) (.local 1)
  let r ← rewritten slots aliases [] e
  checkRun "an ordinary assignment is not a synthetic copy-out" r.body 0 0

  -- Refining dispatch unifies a=b in both the receiver and the borrowed
  -- frame reference, while preserving the checker's canonical local form.
  let parent (a b : VTy) : VTy := .ref [0] [a, b]
  let pair (a b : VTy) : VTy := .ref [1, 2] [a, b]
  let dup (a : VTy) : VTy := .ref [2] [a, a]
  let S : Sigs := {
    fns := [([dup (.var 0), parent (.var 0) (.var 0)], .int)],
    classes := [[.int, pair (.var 0) (.var 1)], [.var 0, .var 1], [.var 0, .var 0]],
    pins := [[none, none], [none, none], [none, some (.var 0)]] }
  let Γ := #[parent (.var 0) (.var 1), pair (.var 0) (.var 1)]
  let e := Expr.ite (.heap (.isTag [2]) [.local 1]) (.call 0 [.local 1, .local 0]) (int (-1))
  let r ← rewritten Γ [{ localSlot := 1, frame := 0, field := 1 }] [] e
  demand "a borrowed receiver has its own typed snapshot slot" (r.slots.size == 3)
  demand "dispatch refines the borrowed frame's type arguments"
    (decide (tc S r.slots.toList .int r.body (some .int) = some .int))

  let e := Expr.forE 1 (.prim .mkArr [int 1]) (.lit .void) (.local 1)
  demand "a generator cannot rebind borrowed storage"
    (match FrameRefs.rewrite slots aliases [] e with | .error _ => true | .ok _ => false)
  IO.println "source-frame rewrite contracts passed"
