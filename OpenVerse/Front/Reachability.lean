/-
  OpenVerse front end — code that is never reached, a warning (the Book of
  Verse's diagnostic 2000: `FlowControl/Reachability.versetest`, "Treat
  unreachable expressions after break as warning not error").
-/
import OpenVerse.Front.Syntax

namespace OpenVerse.Front
namespace Reachability

/-- How an expression ends. `ends`: `none`, it may complete normally; `some
    r`, it never does, always leaving by a `return` or a `break` (or running a
    loop no `break` leaves) or failing, and `r` says whether the code that
    this makes unreachable has been reported already. `fails`: whether it may
    fail (read from the source, so it errs towards yes), which the failure
    context around it takes: an `if`'s condition that may fail before it
    leaves goes on to the `else`. -/
structure Ends where
  ends : Option Bool := none
  fails : Bool := false
  deriving Inhabited

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

/-- A branch with nothing in it (`if{c}`'s, which the parser gives as `{}`). -/
def empty : SExpr → Bool
  | .block _ [] => true
  | _ => false

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

/-- Whether a `set`'s target goes through an index or a key, which may fail. -/
partial def indexes : SExpr → Bool
  | .app _ _ _ true => true
  | .member _ x _ => indexes x
  | _ => false

mutual
/-- `es` run in order: the index of the first that never completes, with
    whether what it makes unreachable is reported (the element after it is
    where the unreachable code starts, reported here), and whether those up to
    it may fail. -/
partial def seqAt (es : List SExpr) (k : Nat := 0) (fails : Bool := false) :
    WM (Option (Nat × Bool) × Bool) := do
  match es with
  | [] => return (none, fails)
  | e :: rest =>
    let r ← go e
    match r.ends with
    | none => seqAt rest (k + 1) (fails || r.fails)
    | some rep =>
      match rest with
      | [] => return (some (k, rep), fails || r.fails)
      | n :: _ =>
        if !rep then reportAt n
        return (some (k, true), fails || r.fails)

/-- The operands of the operation `node`, evaluated in order before it (which
    may fail itself, `own`): when one never completes, the operation is never
    reached. -/
partial def operands (node : SExpr) (es : List SExpr) (own : Bool := false) : WM Ends := do
  let mut fails := false
  for e in es do
    let r ← go e
    fails := fails || r.fails
    if let some rep := r.ends then
      if !rep then reportAt node
      return { ends := some true, fails }
  return { fails := fails || own }

partial def go (e : SExpr) : WM Ends := do
  -- (code marked `@ignore_unreachable`: what it makes unreachable is taken
  -- as reported)
  if (← read).contains e.pos then
    let r ← goRaw e
    return { r with ends := r.ends.map fun _ => true }
  goRaw e

partial def goRaw (e : SExpr) : WM Ends := do
  match e with
  | .ret _ none => return { ends := some false }
  | .ret p (some x) =>
    let r ← go x
    if let some rep := r.ends then
      if !rep then report p
      return { ends := some true, fails := r.fails }
    return { ends := some false, fails := r.fails }
  | .brk _ => return { ends := some false }
  | .block _ es =>
    let (at?, fails) ← seqAt es
    return { ends := at?.map (·.2), fails }
  | .ite p cs t el =>
    let elseOf : WM Ends := match el with
      | some x => go x
      | none => pure {}
    match ← seqAt cs with
    | (some (k, rep), fails) =>
      -- (the branch, when the last clause never completes; the `if`'s value,
      -- when it has none, `if{c}`)
      if k + 1 == cs.length && !rep then (if empty t then report p else reportAt t)
      if k == 0 && !fails then return { ends := some true }
      -- (a clause before it may fail: the `else` is reached)
      let ee ← elseOf
      return { ends := if el.isSome && ee.ends.isSome then some false else none, fails := ee.fails }
    | (none, _) =>
      let te ← go t
      let ee ← elseOf
      return { ends := if el.isSome && te.ends.isSome && ee.ends.isSome then some false else none,
               fails := te.fails || ee.fails }
  | .forE _ cs b =>
    match ← seqAt cs with
    | (some (k, rep), fails) =>
      if k + 1 == cs.length && !rep && !empty b then reportAt b
      return { ends := if k == 0 && !fails then some true else none }
    | (none, _) =>
      let r ← go b
      return { fails := r.fails }
  | .loop _ b =>
    -- (a loop that only a `return` leaves: the code after it is never
    -- reached, `Reachability.versetest:76`; one that nothing leaves, in a
    -- `<suspends>` function, ends when its task is canceled, and the Book's
    -- tests take the code after it without a warning, `Break.versetest:20`)
    let r ← go b
    return { ends := if !hasBreak b && hasReturn b then some false else none, fails := r.fails }
  | .caseE p sc arms =>
    let r ← go sc
    if let some rep := r.ends then
      if !rep then report p
      return { ends := some true, fails := r.fails }
    let mut all := !arms.isEmpty
    let mut fails := r.fails || !arms.any (·.1.isNone)
    for (_, v) in arms do
      let a ← go v
      fails := fails || a.fails
      if a.ends.isNone then all := false
    return { ends := if all then some false else none, fails }
  | .orE _ a b =>
    let ra ← go a
    if let some rep := ra.ends then
      if !ra.fails then
        if !rep then reportAt b
        return { ends := some true }
      return ← go b
    let rb ← go b
    return { fails := rb.fails }
  | .andE _ a b =>
    let ra ← go a
    if let some rep := ra.ends then
      if !rep then reportAt b
      return { ends := some true, fails := ra.fails }
    let rb ← go b
    return { ends := rb.ends, fails := ra.fails || rb.fails }
  | .notE p x =>
    let r ← go x
    if let some rep := r.ends then
      if !r.fails then
        if !rep then report p
        return { ends := some true }
      return {}
    return { fails := true }
  | .optionLit p x | .logicLit p x =>
    let r ← go x
    if let some rep := r.ends then
      if !r.fails then
        if !rep then report p
        return { ends := some true }
    return {}
  | .app _ (.ident _ "$sync") arms _ =>
    let mut any := false
    let mut fails := false
    for a in arms do
      let r ← go a
      fails := fails || r.fails
      if r.ends.isSome then any := true
    return { ends := if any then some false else none, fails }
  | .app _ (.ident _ h) arms _ =>
    if h == "$race" || h == "$rush" then
      let mut all := !arms.isEmpty
      let mut fails := false
      for a in arms do
        let r ← go a
        fails := fails || r.fails
        if r.ends.isNone then all := false
      return { ends := if all then some false else none, fails }
    else if h == "$branch" || h == "$spawn" || h == "$defer" then
      for a in arms do
        let _ ← go a
      return {}
    else if h == "$first" then
      match arms with
      | [.block _ cs] =>
        let (at?, fails) ← seqAt cs
        return { ends := if at?.any (·.1 == 0) && !fails then some true else none, fails := true }
      | _ => operands e e.children true
    else operands e e.children
  | .app _ _ _ bracket => operands e e.children bracket
  | .cmp .. | .query .. => operands e e.children true
  | .set _ l _ _ => operands e e.children (indexes l)
  | .structDef .. | .enumDef .. | .refineDef .. | .typeAlias .. => return {}
  | _ => operands e e.children
end

/-- The code of a program's definitions that is never reached: the bodies of
    its functions and methods, the defaults of their parameters, its
    constants' values and its fields' defaults. -/
partial def ofTop : STop → WM Unit
  | .fn _ _ ps _ _ _ body => do
    for prm in ps do
      if let some d := prm.default then let _ ← go d
    let _ ← go body
  | .const _ _ _ _ (.structDef _ _ _ fs) => do
    for f in fs do
      if let some d := f.default then let _ ← go d
  | .const _ _ _ _ e => do let _ ← go e
  | .classDef _ _ _ _ _ _ _ fs ms => do
    for f in fs do
      if let some d := f.default then let _ ← go d
    for m in ms do ofTop m

/-- Every place where code is never reached, in the program's definitions,
    but after code marked `@ignore_unreachable` (`ignoredArmsMarker`). -/
def warnings (tops : List STop) : Array (Pos × String) :=
  let ignored := tops.flatMap fun
    | .const _ n _ _ (.block _ es) => if n == ignoredArmsMarker then es.map (·.pos) else []
    | _ => []
  (((tops.forM ofTop).run ignored).run #[]).2

end Reachability
end OpenVerse.Front
