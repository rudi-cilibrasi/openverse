/-
  OpenVerse front end — code that is never reached, a warning (the Book of
  Verse's diagnostic 2000: `FlowControl/Reachability.versetest`, "Treat
  unreachable expressions after break as warning not error").
-/
import OpenVerse.Front.Syntax

namespace OpenVerse.Front
namespace Reachability

/-- How an expression ends: `none`, it may complete normally; `some r`, it
    never does, always leaving by a `return` or a `break` (or running a loop
    only a `return` leaves), and `r` says whether the code this makes
    unreachable has been reported already.

    No failure context's code ever ends, so whether code may fail is never
    asked: `checkJumps` refuses a `return` in an `if`'s conditions, a `for`'s
    clauses, `first`, `option{…}`, `logic{…}`, `not`'s operand and the left
    of `or`, and a `break` there but in a loop of its own, which a `break`
    cannot make end; and nothing else ends code here (a loop that nothing
    leaves, a call of a function that never returns and `Err()` complete as
    far as this pass knows). -/
abbrev Ends := Option Bool

/-- The warnings found so far, each with where it is, under the positions of
    the code marked `@ignore_unreachable` (Book of Verse ch. 12; its tests,
    `Reachability.versetest:94`: "can be used on a break/return to suppress
    unreachable warnings in subsequent code"). -/
abbrev WM := ReaderT (List Pos) (StateM (Array (Pos × String)))

def message : String :=
  "this code is never reached: the code before it always returns or breaks"

def report (p : Pos) : WM Unit := modify (·.push (p, message))

/-- Report the code that starts with `e`. -/
def reportAt (e : SExpr) : WM Unit := report e.start

/-- Whether `e` has a `break` of the loop it is in: one in no loop of its own,
    nor in a `branch:`, `spawn` or `defer:` body (a `break` in a `for`'s body
    leaves the loop around the `for`, the Book's
    `SOL-4199-BreakFromIf.versetest:38`). -/
partial def hasBreak : SExpr → Bool
  | .brk _ => true
  | .loop .. => false
  | e@(.app _ (.ident _ h) _ _) =>
    if h == "$branch" || h == "$spawn" || h == "$defer" then false else e.children.any hasBreak
  | e => e.children.any hasBreak

/-- Whether `e` has a `return`, but in a `branch:`, `spawn` or `defer:` body. -/
partial def hasReturn : SExpr → Bool
  | .ret .. => true
  | e@(.app _ (.ident _ h) _ _) =>
    if h == "$branch" || h == "$spawn" || h == "$defer" then false else e.children.any hasReturn
  | e => e.children.any hasReturn

mutual
/-- `es` run in order: how the first that never completes ends (the element
    after it is where the unreachable code starts, reported here). -/
partial def seq : List SExpr → WM Ends
  | [] => return none
  | e :: rest => do
    match ← go e with
    | none => seq rest
    | some rep =>
      match rest with
      | [] => return some rep
      | n :: _ =>
        if !rep then reportAt n
        return some true

/-- The operands of the operation `node`, evaluated in order before it: when
    one never completes, the operation is never reached. -/
partial def operands (node : SExpr) (es : List SExpr) : WM Ends := do
  for e in es do
    if let some rep ← go e then
      if !rep then reportAt node
      return some true
  return none

/-- Code in a failure context, which always completes or fails (`Ends`): the
    code in it never reached. -/
partial def inContext (e : SExpr) : WM Unit := discard (go e)

partial def go (e : SExpr) : WM Ends := do
  -- (code marked `@ignore_unreachable`: what it makes unreachable is taken
  -- as reported)
  if (← read).contains e.pos then
    return (← goRaw e).map fun _ => true
  goRaw e

partial def goRaw (e : SExpr) : WM Ends := do
  match e with
  | .ret _ none => return some false
  | .ret p (some x) =>
    if let some rep ← go x then
      if !rep then report p
      return some true
    return some false
  | .brk _ => return some false
  | .block _ es => seq es
  | .ite _ cs t el =>
    cs.forM inContext
    let te ← go t
    let ee ← el.mapM go
    return if te.isSome && (ee.bind id).isSome then some false else none
  | .forE _ cs b =>
    -- (a `break` in its body leaves the loop around it, and it may run its
    -- body no time)
    cs.forM inContext
    discard (go b)
    return none
  | .loop _ b =>
    -- (a loop that only a `return` leaves: the code after it is never
    -- reached, `Reachability.versetest:76`; one that nothing leaves, in a
    -- `<suspends>` function, ends when its task is canceled, and the Book's
    -- tests take the code after it without a warning, `Break.versetest:20`)
    discard (go b)
    return if !hasBreak b && hasReturn b then some false else none
  | .caseE p sc arms =>
    if let some rep ← go sc then
      if !rep then report p
      return some true
    let mut all := !arms.isEmpty
    for (_, v) in arms do
      if (← go v).isNone then all := false
    return if all then some false else none
  | .orE _ a b =>
    inContext a
    discard (go b)
    return none
  | .andE _ a b =>
    if let some rep ← go a then
      if !rep then reportAt b
      return some true
    go b
  | .notE _ x | .optionLit _ x | .logicLit _ x =>
    inContext x
    return none
  | .app _ (.ident _ "$sync") arms _ =>
    let mut any := false
    for a in arms do
      if (← go a).isSome then any := true
    return if any then some false else none
  | .app _ (.ident _ h) arms _ =>
    if h == "$race" || h == "$rush" then
      let mut all := !arms.isEmpty
      for a in arms do
        if (← go a).isNone then all := false
      return if all then some false else none
    else if h == "$branch" || h == "$spawn" || h == "$defer" then
      arms.forM fun a => discard (go a)
      return none
    else operands e e.children
  | .structDef .. | .enumDef .. | .refineDef .. | .typeAlias .. => return none
  | _ => operands e e.children
end

/-- The code of a definition that is never reached (`STop.code`: the
    bodies of its functions and methods, the defaults of their parameters,
    its constants' values and its fields' defaults). -/
def ofTop (t : STop) : WM Unit :=
  t.code.forM fun e => do let _ ← go e

/-- Every place where code is never reached, in the program's definitions,
    but after code marked `@ignore_unreachable` (`ignoredArmsMarker`). -/
def warnings (tops : List STop) : Array (Pos × String) :=
  (((tops.forM ofTop).run (ignoredArmsOf tops)).run #[]).2

end Reachability
end OpenVerse.Front
