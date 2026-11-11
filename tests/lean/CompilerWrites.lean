/- Implementation writes must not erase unrelated Core read-only checks. -/
import OpenVerse.Front.CompilerWrites
import OpenVerse.Core.Check

open OpenVerse OpenVerse.Front

private def demand (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

private def fn (name : String) (body : Expr) (writes : Bool := false) : Fn :=
  { name, body, writes, arity := 0, nslots := 1, decides := false }

private def flags (fns : Array Fn) : List Bool := fns.toList.map (·.writes)
private def checked (fns : Array Fn) : Bool := ({ fns := fns.toList, main := 0 } : Prog).checkWriteSound
private def int (n : Int) : Expr := .lit (.int n)

def main : IO Unit := do
  -- Reverse declaration order requires a fixed point, not one forward pass.
  let before := #[fn "outer" (.call 1 []), fn "middle" (.call 2 []), fn "start" (int 7)]
  let after := before.set! 2 (fn "start" (.heap (.set 0) [.lit (.ref 0), int 7]) true)
  demand "the newly writing callee invalidates its callers" (!checked after)
  let out := CompilerWrites.propagate before after
  demand "reverse caller chain" (flags out == [true, true, true] && checked out)

  let before := #[fn "a" (.call 1 []), fn "b" (.seq (.call 0 []) (.call 2 [])), fn "start" (int 7)]
  let after := before.set! 2 (fn "start" (int 7) true)
  demand "recursive caller component" (flags (CompilerWrites.propagate before after) == [true, true, true])

  -- A new implementation helper has no source permission to propagate.
  let before := #[fn "caller" (int 0)]
  let after := #[fn "caller" (.call 1 []), fn "implementation" (int 7) true]
  demand "new implementation function" (flags (CompilerWrites.propagate before after) == [true, true])

  let writer := fn "user-writer" (.heap (.set 0) [.lit (.ref 0), int 9]) true
  let before := #[fn "bad-reader" (.call 1 []), writer, fn "start" (int 7)]
  let after := before.set! 2 (fn "start" (int 7) true)
  let out := CompilerWrites.propagate before after
  demand "existing writer is not a compiler seed" (flags out == [false, true, true] && !checked out)
  demand "without implementation changes the guard is unchanged"
    (flags (CompilerWrites.propagate before before) == [false, true, false] && !checked before)

  let before := #[fn "bad-store" (.heap (.set 0) [.lit (.ref 0), int 9]), fn "start" (int 7)]
  let after := before.set! 1 (fn "start" (int 7) true)
  let out := CompilerWrites.propagate before after
  demand "an unrelated intrinsic store still fails" (flags out == [false, true] && !checked out)

  let contexts : List Expr := [
    .call 2 [.call 1 []], .assign 0 (.call 1 []), .ret (.call 1 []), .print (.call 1 []),
    .loop (.call 1 []), .seq (int 0) (.call 1 []), .prim .mkArr [.call 1 []],
    .heap (.new 0) [.call 1 []], .ite (int 0) (.call 1 []) (int 0),
    .forE 0 (.lit (.arr #[])) (int 0) (.call 1 [])]
  for e in contexts do
    let before := #[fn "caller" e, fn "start" (int 7), fn "other" (int 0)]
    let after := before.set! 1 (fn "start" (int 7) true)
    demand "nested call traversal" (flags (CompilerWrites.propagate before after) == [true, true, false])
  IO.println "compiler write-flag contracts passed"
