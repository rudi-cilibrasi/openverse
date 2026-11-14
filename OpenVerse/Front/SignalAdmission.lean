/-
  (#515, `--signal-no-rollback`) An opt-in admission policy for event
  signals in failure contexts: the published API renders an event's
  `Signal` `<no_rollback>`, which a failure context cannot use, while
  openverse's reference mode rolls a signal back with its context. Under
  the policy, a program that may call an event's `Signal` from a failure
  context is refused before it runs or is emitted.

  The functions that may signal are found on the elaborated Verse Core,
  before the concurrency lowering: those from which the prelude's
  `signalAll` (which every kind of event's `Signal` calls) is reachable
  through calls, also through a method's dispatch and a function value's,
  which are calls in Verse Core (so callbacks count, conservatively). The
  failure contexts are the elaborator's (`Ctx.canFail`: an if's condition,
  a for's filter, a `<decides>` function's body, …), where it records the
  functions each call calls (`ESt.failCalls`). A `for`'s body that the
  choice lowering puts in a continuation of its own (`continuation`) is
  still not one: the continuation is not followed from a call, and its
  own failure contexts are recorded where it is elaborated.
-/
import OpenVerse.Core.Syntax
import Std.Data.HashMap
import Std.Data.HashSet

namespace OpenVerse.Front.SignalAdmission
open OpenVerse

mutual
/-- The functions an expression calls, anywhere in it, except the one a
    `spawn` runs (`spawn`: the prelude's `$spawnMark`, whose argument is
    `array{F(…)}`): its task runs it later, outside the failure context
    (its arguments, evaluated at once, count). -/
partial def calls (spawn : Option Nat) : Expr → List Nat
  | .call f es => if spawn == some f then es.flatMap (spawned spawn) else f :: es.flatMap (calls spawn)
  | .lit _ | .local _ | .brk => []
  | .assign _ e | .loop e | .ret e | .print e => calls spawn e
  | .seq a b => calls spawn a ++ calls spawn b
  | .prim _ es | .heap _ es => es.flatMap (calls spawn)
  | .ite c t e => calls spawn c ++ calls spawn t ++ calls spawn e
  | .forE _ a f b => calls spawn a ++ calls spawn f ++ calls spawn b

/-- A `spawn`'s argument: its call's arguments, not the function. -/
partial def spawned (spawn : Option Nat) : Expr → List Nat
  | .call _ es => es.flatMap (calls spawn)
  | .seq a b => spawned spawn a ++ spawned spawn b
  | .prim _ es => es.flatMap (spawned spawn)
  | e => calls spawn e
end

/-- A function's name as the source writes it (the prelude's names start
    with `$`; a class's `block:` is its `C.$block`). -/
def shown (n : String) : String :=
  let n := if n.startsWith "$" then (n.drop 1).toString else n
  if n.endsWith ".$block" then s!"{String.ofList (n.toList.take (n.length - 7))}'s block" else n

/-- The function a name stands for, without its wrapper's suffix
    (`K$init`, a constructor function; `F$ov1`, an overload; `C$M$fn.$call…`,
    `C.M` called as a function value, as the error message reads them),
    so that a step through a wrapper is shown once. -/
def stem (n : String) : String :=
  let n := if n.startsWith "$" then (n.drop 1).toString else n
  match n.splitOn "$fn.$call" with
  | f :: _ :: _ => f.replace "$" "."
  | _ => String.ofList (n.toList.takeWhile (· != '$'))

/-- `way` without a step that repeats the one before it (`stem`). -/
def tidy : List String → List String
  | a :: b :: rest => if stem a == stem b then tidy (a :: rest) else a :: tidy (b :: rest)
  | way => way

/-- The functions that may signal: each with the function it calls on a
    way to `signalAll` (`none` for `signalAll` itself). -/
def maySignal (fns : Array Fn) : Std.HashMap Nat (Option Nat) := Id.run do
  let spawn := fns.findIdx? (·.name == "$spawnMark")
  let callees := fns.map fun fn => (calls spawn fn.body).eraseDups
  let mut ms : Std.HashMap Nat (Option Nat) := {}
  for i in [0:fns.size] do
    if fns[i]!.name == "$signalAll" then ms := ms.insert i none
  let mut grew := true
  while grew do
    grew := false
    for i in [0:fns.size] do
      if !ms.contains i then
        if let some f := callees[i]!.find? ms.contains then
          ms := ms.insert i (some f)
          grew := true
  return ms

/-- (event mode, docs/research/scheduler-conformance.md, "Awaiters run
    inside `Signal`") The functions from which `signalAll` is reachable
    through calls, a spawned call's included (a `spawn` runs it to its first
    wait at once): the suspends functions among them are the ones whose code
    may be running while a `Signal` runs, which the lowering marks. -/
def reaching (fns : Array Fn) : Std.HashSet Nat := Id.run do
  let callees := fns.map fun fn => (calls none fn.body).eraseDups
  let mut ms : Std.HashSet Nat := {}
  for i in [0:fns.size] do
    if fns[i]!.name == "$signalAll" then ms := ms.insert i
  let mut grew := true
  while grew do
    grew := false
    for i in [0:fns.size] do
      if !ms.contains i then
        if callees[i]!.any ms.contains then
          ms := ms.insert i
          grew := true
  return ms

/-- The way from function `f` to an event's `Signal`, by name: up to the
    first `Signal` method on it (else to `signalAll`). -/
partial def path (fns : Array Fn) (ms : Std.HashMap Nat (Option Nat)) (f : Nat) (fuel : Nat := 64) : List String :=
  let n := ((fns[f]?).map (·.name)).getD "?"
  if n.endsWith ".Signal" || fuel == 0 then [shown n] else
  match ms.get? f with
  | some (some g) => shown n :: path fns ms g (fuel - 1)
  | _ => [shown n]

/-- A `for`'s continuation (#335): the clauses after a choice and the
    body, in a function of their own that each alternative's filter calls.
    Its clauses are failure contexts recorded where it is elaborated, and
    its body is not one, unless the `for`'s own is or the `for` is inside
    one (`FirstLift.rollback` starts its frame with `Ctx.inRollback`), so a
    call of it is not followed from a failure context. -/
def continuation (n : String) : Bool := n.startsWith "$contf"

/-- The first call in a failure context (`sites`, recorded by the
    elaborator where it is in one: an if's condition, a for's filter, a
    `<decides>` function's body, …) that
    calls a function that may signal, with the way to the `Signal`. -/
def checkSites {α : Type} (fns : Array Fn) (sites : Array (α × List Nat)) : Option (α × List String) := Id.run do
  let ms := maySignal fns
  if ms.isEmpty then return none
  let followed (f : Nat) : Bool :=
    ms.contains f && !(fns[f]?.any fun fn => continuation fn.name)
  for (p, callees) in sites do
    if let some f := callees.find? followed then return some (p, tidy (path fns ms f))
  return none

end OpenVerse.Front.SignalAdmission
