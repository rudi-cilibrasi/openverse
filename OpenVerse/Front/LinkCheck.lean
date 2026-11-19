/-
  Module constants that allocate a `var` (#724). Epic's Verse VM computes a
  module's constants when it links the program (the session's server cook,
  UEFN 43.12), and allocating a mutable variable there is a runtime error
  that fails the link: "Script error 9003: Runtime error while evaluating
  module." The Book's tests expect the same (`GlobalVariables.versetest`
  86, 90, 97, 105, `verse_vm_only` link errors), with a control that links
  because the `var` is on a path its initialiser does not take (`:143`).
  OpenVerse computes a constant at each use, so it has no such phase; this
  check is that phase's rule, applied before the program is emitted or run.

  Allocating a `var` is declaring a `var` local of the source, in the
  constant's initialiser or in any code it runs (a function it calls, a
  class's `block:`), or constructing an object of a class with a `var`
  field. Which ones an initialiser allocates depends on the path it takes,
  so the constant is computed, at compile time, by the reference
  interpreter, on a copy of the program in which each such allocation
  prints its number and stops the evaluation with a slot error, which no
  checked program raises (`Eval.scoped_ok`). Only constants from which some
  such allocation is reachable through calls are computed; the others,
  almost all, are not. A computation that fails, raises another error, or
  does not end within the fuel given is left alone: it behaves at run time
  as before.
-/
import OpenVerse.Core.Bounded
import OpenVerse.Core.Typing
import OpenVerse.Front.Suspend
import OpenVerse.Front.Syntax
import Std.Data.HashSet

namespace OpenVerse.Front.LinkCheck
open OpenVerse

/-- What a site allocates, said for the error. -/
abbrev Sites := StateM (Array String)

/-- A function's name as the source has it. -/
def shown (n : String) : String :=
  match n.splitOn ".$block" with
  | [c, ""] => s!"the block of {c}"
  | _ => n

/-- The code of an allocation site: its number printed, then a call of
    `marker`, which stops the evaluation; `what` it allocates kept for the
    error. -/
def mark (marker : Nat) (what : String) : Sites Expr := do
  let k := (← get).size
  modify (·.push what)
  return .seq (.print (.lit (Value.ofString (toString k)))) (.call marker [])

/-- `e` with each allocation of a `var` (a source `var` local's slot
    assigned, `vars`: its declaration, or a `set` after it in the same call;
    a construction of a class in `varTags`) preceded by its `mark`. -/
partial def instrument (fname : String) (vars : List (Nat × String)) (varTags : List (Nat × String))
    (marker : Nat) : Expr → Sites Expr
  | .assign i e => do
    let e' ← instrument fname vars varTags marker e
    match vars.lookup i with
    | some x =>
      let m ← mark marker s!"the var {x} declared in {shown fname}"
      return Expr.seq m (Expr.assign i e')
    | none => return Expr.assign i e'
  | .heap op es => do
    let es' ← es.mapM (instrument fname vars varTags marker)
    let made : Option String := match op with
      | .new t => varTags.lookup t
      | _ => none
    match made with
    | some c =>
      let m ← mark marker s!"an object of class {c}, which has a var field, made in {shown fname}"
      return Expr.seq m (Expr.heap op es')
    | none => return Expr.heap op es'
  | .seq a b => do
    let a' ← instrument fname vars varTags marker a
    let b' ← instrument fname vars varTags marker b
    return Expr.seq a' b'
  | .prim p es => do return Expr.prim p (← es.mapM (instrument fname vars varTags marker))
  | .call f es => do return Expr.call f (← es.mapM (instrument fname vars varTags marker))
  | .ite c t e => do
    let c' ← instrument fname vars varTags marker c
    let t' ← instrument fname vars varTags marker t
    let e' ← instrument fname vars varTags marker e
    return Expr.ite c' t' e'
  | .forE i it f b => do
    let it' ← instrument fname vars varTags marker it
    let f' ← instrument fname vars varTags marker f
    let b' ← instrument fname vars varTags marker b
    return Expr.forE i it' f' b'
  | .loop b => do return Expr.loop (← instrument fname vars varTags marker b)
  | .ret e => do return Expr.ret (← instrument fname vars varTags marker e)
  | .print e => do return Expr.print (← instrument fname vars varTags marker e)
  | e => return e

/-- Whether `e` constructs an object of a class in `varTags`. -/
partial def constructs (varTags : List (Nat × String)) : Expr → Bool
  | .heap (.new t) es => (varTags.lookup t).isSome || es.any (constructs varTags)
  | .heap _ es | .prim _ es | .call _ es => es.any (constructs varTags)
  | .assign _ e | .loop e | .ret e | .print e => constructs varTags e
  | .seq a b => constructs varTags a || constructs varTags b
  | .ite c t e => constructs varTags c || constructs varTags t || constructs varTags e
  | .forE _ a f b => constructs varTags a || constructs varTags f || constructs varTags b
  | _ => false

/-- A function's initialisations and the rest of its body. -/
def split (fn : Fn) : List Expr × Expr :=
  (Suspend.stripInits (fn.nslots - fn.arity) fn.body).getD ([], fn.body)

/-- The functions reachable from `f` through calls (`f` among them). -/
partial def reach (fns : Array Fn) (f : Nat) : List Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut todo : List Nat := [f]
  let mut out : List Nat := []
  while true do
    match todo with
    | [] => break
    | g :: rest =>
      todo := rest
      if seen.contains g then continue
      seen := seen.insert g
      out := g :: out
      if let some fn := fns[g]? then
        for (h, _) in Suspend.callsOf fn.body do
          if !seen.contains h then todo := h :: todo
  return out.reverse

/-- Whether code in `fns[g]` allocates a `var`: a source `var` local, or a
    construction of a class in `varTags` (outside its initialisations). -/
def allocates (fns : Array Fn) (vars : Array (List (Nat × String))) (varTags : List (Nat × String))
    (g : Nat) : Bool :=
  match fns[g]? with
  | some fn => !(vars[g]?.getD []).isEmpty || constructs varTags (split fn).2
  | none => false

/-- The fuel and the depth a constant's computation is given. -/
def fuel : Nat := 2000000
def depth : Nat := 2000

/-- The number a run printed last, the site that stopped it. -/
def lastSite (out : List Nat) : Option Nat :=
  let line := (out.reverse.drop 1).takeWhile (· != 10) |>.reverse
  if line.isEmpty || !line.all (fun b => 48 ≤ b && b ≤ 57) then none
  else some (line.foldl (fun n b => 10 * n + (b - 48)) 0)

/-- The first constant of `consts` (its function, its name as written and
    its position) whose computation allocates a `var`, with what it
    allocates, if any. `fns` are the program's functions before the
    lowering, `vars` each one's slots of source `var` locals with their
    names, `varTags` the classes with a `var` field, and `protos` the
    prototypes the program starts by allocating. -/
def firstAllocating (fns : Array Fn) (vars : Array (List (Nat × String))) (varTags : List (Nat × String))
    (protos : List (Nat × List Value)) (consts : List (Nat × String × Pos)) :
    Option (String × Pos × String) := Id.run do
  let marker := fns.size
  -- (the marker: a function with no slot that writes one)
  let markerFn : Fn := { name := "$linkVar", arity := 0, nslots := 0, decides := false,
                         writes := false, body := .assign 0 (.lit .void) }
  let mut instrumented : Option (Prog × Array String) := none
  for (f, name, p) in consts do
    let r := reach fns f
    if !r.any (allocates fns vars varTags) then continue
    let (P, sites) ← match instrumented with
      | some x => pure x
      | none =>
        let (fs, sites) := (fns.mapIdxM fun g fn => do
          let (ds, b) := split fn
          let b' ← instrument fn.name (vars[g]?.getD []) varTags marker b
          return { fn with body := initPrefixE fn.arity ds b' }).run #[]
        pure ({ fns := (fs.push markerFn).toList, main := f }, sites)
    instrumented := some (P, sites)
    match evalB P fuel depth Prog.initSt (protoPrelude protos (.call f [])) with
    | .res (.err .slot, s) =>
      let what := ((lastSite s.g.out).bind (sites[·]?)).getD "a var"
      return some (name, p, what)
    | _ => pure ()
  return none

end OpenVerse.Front.LinkCheck
