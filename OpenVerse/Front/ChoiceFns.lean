/-
  OpenVerse front end — functions with several values (#235): what they
  are, the shapes of the recursive ones that are taken lazily, their
  `return`s, their calls inlined (`inlineCalls`), a `for` whose body has
  several values, and methods and overloads with several values as
  functions of their own (`methodFns`). The surface side of a choice and
  its lifting out of an expression are in `ChoiceLift.lean`; what puts
  these together for a program is in `Choice.lean`.
-/
import OpenVerse.Front.ChoiceLift

namespace OpenVerse.Front.Choice

/-! ### Functions with several values (#235)

A top-level function whose body has a choice that no failure context in
it takes (`Digit():int = 0 | 1 | … | 9`) has several values. A call of one
is a choice point: `inlineMulti` drops the function and turns each call into
`$inline(F, template, args…)`, whose template is the body with its
parameters and locals renamed for that call; lifting (`liftE`) puts the
arguments into the parameters, then the body's clauses, into the caller's
clauses, so the body's choices become the caller's. Recursive and generic
ones, ones with named parameters or `return`, and their use as values are
refused for now. -/

/-- A function of the program, by name: its parameters, type parameters,
    effects, result type and body. -/
structure MFn where
  pos : Pos
  params : List SParam
  tparams : List TParam
  fx : List String
  ret : STy
  body : SExpr

/-- A mutual producer's written types have their own lexical aliases,
    separate from the consumer's and from the actual Core type names. -/
def memberTypeName (member param : String) : String := s!"$groupType_{member}_{param}"

/-- The names `e` uses as identifiers and call heads, in first-use order. -/
partial def namesUsed (e : SExpr) : List String :=
  let rec go : SExpr → List String
    | .app _ (.ident _ "$constructHints") _ false => []
    | .ident _ n => [n]
    -- (a struct's field defaults, which `children` leaves out)
    | .structDef _ _ _ fs => fs.flatMap fun f => (f.default.map go).getD []
    | e => e.children.flatMap go
  let (_, names) := (go e).foldl (fun (seen, names) n =>
    if seen.contains n then (seen, names) else (seen.insert n, n :: names))
    (({} : Std.HashSet String), [])
  names.reverse

/-- Whether a written type mentions one of the names `tps`. -/
partial def styMentions (tps : List String) : STy → Bool
  | .name n => tps.contains n
  | .arr t | .opt t => styMentions tps t
  | .tup ts => ts.any (styMentions tps)
  | .map k v => styMentions tps k || styMentions tps v
  | .app n ts => tps.contains n || ts.any (styMentions tps)
  | .fn ps _ r => ps.any (styMentions tps) || styMentions tps r

/-- `e` with each overridden method's dispatch (#283) a block: the receiver
    and the arguments into the template's names, then its exclusive choice,
    then its value. For a body not inlined (an `F$all`'s, effect-free). -/
partial def dispatchBlocks (e : SExpr) : SExpr :=
  mapE (fun
    | .app _ (.ident _ "$dispatch") (_ :: .block bp tmpl :: as) false =>
      -- (a generic family's, #283: its receiver and arguments bound
      -- together, `$params`, as `bindParams` binds them where the call is
      -- inlined, so the receiver is at the declaring class here too, and
      -- the type parameters are named for the written types after)
      let (marks, tmpl) := match tmpl with
        | m@(.app _ (.ident _ "$tparams") _ false) :: rest => ([m], rest)
        | _ => ([], tmpl)
      let binds := (tmpl.zip as).map fun
        | (.decl q x t v _, a) => SExpr.decl q x t v (dispatchBlocks a)
        | (d, _) => d
      let binds := match marks with
        | [.app _ _ tps _] => [.app bp (.ident bp "$params") (.block bp binds :: tps) false]
        | _ => binds
      let val : List SExpr := match tmpl.getLast? with
        | some (.decl q x _ _ _) => [.ident q x]
        | _ => []
      some (.block bp (binds ++ (tmpl.drop as.length).map dispatchBlocks ++ val))
    | _ => none) e

/-- `e` with every choice `a₁ | … | aₙ` made `if (false?) then a₁ else …
    aₙ`: the body a function with several values keeps, elaborated (so
    type- and effect-checked like any function's) but never called, as its
    calls are inlined. -/
partial def checkBody : SExpr → SExpr :=
  mapE fun
    -- The cursor elaborator prepares the header itself. Scalarizing its
    -- choices here would change the saved frame's layout.
    | e@(.app _ (.ident _ "$forCursorNext") _ false)
      | e@(.app _ (.ident _ "$forOwnedCursorNext") _ false)
      | e@(.app _ (.ident _ "$forNestedCursorNext") _ false)
      | e@(.app _ (.ident _ "$noteForCursor") _ false) => some e
    | .app p (.ident _ "$methodMiss") [] false => some (.app p (.ident p "Err") [] false)
    -- (an exclusive choice, #314: an if-chain on its guards)
    | .app p (.ident _ "$excl") alts false =>
      some (alts.foldr (fun a acc => match a with
        | .app _ (.ident _ "$alt") [.block bp gs, rest] false => .ite bp (gs.map checkBody) (checkBody rest) (some acc)
        | _ => acc) (.app p (.ident p "Err") [] false))
    -- (a method's dispatch on the receiver's class, #283: the receiver and
    -- the arguments into the template's names, then its exclusive choice,
    -- an if-chain whose end a call never reaches, then its value)
    | d@(.app _ (.ident _ "$dispatch") _ false) =>
      match dispatchBlocks d with
      | .block bp ss => some (.block bp (ss.map checkBody))
      | _ => none
    | .app p (.ident _ "$choice") as false =>
      let rec chain : List SExpr → SExpr
        | [] => .tuple p []
        | [a] => checkBody a
        | a :: rest => .ite p [.query p (.ident p "false")] (checkBody a) (some (chain rest))
      some (chain as)
    | _ => none

/-- A written type with the names of `ρ` renamed. -/
partial def styRename (ρ : List (String × String)) : STy → STy
  | .name n => .name ((ρ.lookup n).getD n)
  | .arr t => .arr (styRename ρ t)
  | .opt t => .opt (styRename ρ t)
  | .tup ts => .tup (ts.map (styRename ρ))
  | .map k v => .map (styRename ρ k) (styRename ρ v)
  | .app n ts => .app ((ρ.lookup n).getD n) (ts.map (styRename ρ))
  | .fn ps es r => .fn (ps.map (styRename ρ)) es (styRename ρ r)

/-- The types a body writes (bindings', constructions' type arguments) with
    the names of `ρ` renamed: a generic function's type parameters, renamed
    for the site its body is inlined at (#235). -/
partial def renameTypes (ρ : List (String × String)) : SExpr → SExpr :=
  mapE fun
    | .decl p n (some t) v x => some (.decl p n (some (styRename ρ t)) v (renameTypes ρ x))
    | .construct p n ts fs => some (.construct p ((ρ.lookup n).getD n) (ts.map (styRename ρ)) (fs.map (renameTypes ρ)))
    | _ => none

/-- Split a tail block without losing the value of its final binding. -/
def loopBlockParts (p : Pos) (ss : List SExpr) : List SExpr × SExpr :=
  match ss.getLast? with
  | none => ([], .tuple p [])
  | some (.decl q x ..) => (ss, .ident q x)
  | some value => (ss.dropLast, value)

/-- An incomplete source conditional discards its values, including in a
    nested tail block. Recursive edges still yield their erased result. -/
partial def completeLoopTail (isRec : SExpr → Bool) (discarded : Bool) : SExpr → SExpr
  | .app p (.ident q "$returnTail") [.block r ss] false =>
    let (pre, value) := loopBlockParts r ss
    .app p (.ident q "$returnTail") [.block r (pre ++ [completeLoopTail isRec discarded value])] false
  | e@(.ite p cs t u) =>
    let erased := discarded || !isBranchy.complete e
    .ite p cs (completeLoopTail isRec erased t)
      (some (completeLoopTail isRec erased (u.getD (.tuple p []))))
  | e =>
    let discard (a : SExpr) := if isRec a then a else
      .block a.pos [.decl a.pos "$discard" (some (.name "void")) false a]
    if !discarded then e else match alts? e with
      | some as => mk e.pos (as.map discard)
      | none => discard e

/-- Invocation-path markers are consumed by lazy lowering. Eager array
    lowering uses the same normalized body as ordinary source blocks. -/
partial def eraseReturnTails : SExpr → SExpr :=
  mapE fun
    | .app _ (.ident _ "$returnTail") [body] false => some (eraseReturnTails body)
    | _ => none

/-- Visit only the value leaves of a recursive tail, retaining path scopes. -/
partial def mapLoopTail (leaf : SExpr → SExpr) : SExpr → SExpr
  | .app _ (.ident _ "$returnTail") [.block p ss] false =>
    let (pre, value) := loopBlockParts p ss
    -- Keep prepared consumer suffixes behind a taking boundary, so
    -- branch-block renaming cannot give each copy a new helper identity.
    let result := s!"$returnPath{p.line}_{p.col}"
    .app p (.ident p "$first") [.block p (pre ++
      [.decl p result none false (mapLoopTail leaf value), .ident p result])] false
  | .ite p cs t u => .ite p cs (mapLoopTail leaf t) (u.map (mapLoopTail leaf))
  | e => leaf e

partial def loopTailOK (plain groupOK : SExpr → Bool) : SExpr → Bool
  | .app _ (.ident _ "$returnTail") [.block p ss] false =>
    let (pre, value) := loopBlockParts p ss
    pre.all plain && loopTailOK plain groupOK value
  | .ite _ cs t (some u) => cs.all plain && loopTailOK plain groupOK t && loopTailOK plain groupOK u
  | e => groupOK e

/-- A recursive tail with each `if` in a branch's place that has no choice
    and no call of the group in it (`plain`, no returning path) made a block:
    a value, whose conditions run with it and are undone with it, as any
    value's code is, not a branch the invocation selects once for all its
    values. The tail's own `if` stays its branch. -/
partial def plainIfValues (plain : SExpr → Bool) : SExpr → SExpr
  | .app p (.ident q "$returnTail") [.block r ss] false =>
    let (pre, value) := loopBlockParts r ss
    .app p (.ident q "$returnTail") [.block r (pre ++ [leaf value])] false
  | .ite p cs t u => .ite p cs (leaf t) (u.map leaf)
  | e => e
where
  leaf (e : SExpr) : SExpr := match e with
    | .ite p .. =>
      if plain e && !anyE (fun | .app _ (.ident _ "$returnTail") _ false => true | _ => false) e then .block p [e]
      else plainIfValues plain e
    | e => plainIfValues plain e

/-- Visit the value leaves of a recursive tail, keeping its path scopes as
    they are (`mapLoopTail` puts each behind a taking boundary instead). -/
partial def mapLoopLeaves (leaf : SExpr → SExpr) : SExpr → SExpr
  | .app p (.ident q "$returnTail") [.block r ss] false =>
    let (pre, value) := loopBlockParts r ss
    .app p (.ident q "$returnTail") [.block r (pre ++ [mapLoopLeaves leaf value])] false
  | .ite p cs t u => .ite p cs (mapLoopLeaves leaf t) (u.map (mapLoopLeaves leaf))
  | e => leaf e

/-- `mapLoopLeaves`, each leaf with its index, in order. -/
partial def mapLoopLeavesIdx (leaf : Nat → SExpr → SExpr) (e : SExpr) : SExpr :=
  (go e).run' 0
where
  go : SExpr → StateM Nat SExpr
    | .app p (.ident q "$returnTail") [.block r ss] false => do
      let (pre, value) := loopBlockParts r ss
      return .app p (.ident q "$returnTail") [.block r (pre ++ [← go value])] false
    | .ite p cs t u => do
      let t' ← go t
      return .ite p cs t' (← u.mapM go)
    | e => do
      let i ← get
      set (i + 1)
      return leaf i e

/-- (#283) A function's body with its own `defer:`s after each value of its
    last expression (`deferLast`'s placing, leaf by leaf, `mapLoopLeaves`):
    so they run as each value leaves it, and an `if` that ends it still picks
    its branch as the function's path, as without them, its conditions the
    call's code, not each value's. As `deferLast` when that expression has an
    `if` with no `else` among its branches, or is not a value. -/
def deferLastLeaves (p : Pos) (ss : List SExpr) : List SExpr :=
  if !ss.any isDefer || ss.getLast?.any isDefer then deferLast p (madeName "dv" "" p) ss else
  let (stmts, ds) := pendingIn [] ss
  let run := SExpr.block p (ds ++ [.int p 0])
  let vals := ss.filterMap fun | .decl _ x _ false _ => some x | _ => none
  let leaf (v : SExpr) : SExpr :=
    if pureVal vals v then .block v.pos [run, v] else
    let dv := madeName "dv" "" v.pos
    .block v.pos [.decl v.pos dv none false v, run, .ident v.pos dv]
  let rec complete : SExpr → Bool
    | .ite _ _ t (some u) => complete t && complete u
    | .ite _ _ _ none => false
    | _ => true
  match stmts.getLast? with
  | some (.decl q x t false rhs) =>
    if complete rhs then stmts.dropLast ++ [.decl q x t false (mapLoopLeaves leaf rhs)]
    else deferLast p (madeName "dv" "" p) ss
  | some l => if complete l then stmts.dropLast ++ [mapLoopLeaves leaf l] else deferLast p (madeName "dv" "" p) ss
  | none => ss

/-- (#283) The frame code of an `if`'s leaves after its first, which has the
    code: the frame is that one, its hole's last (`loopFlatWith`), so the
    code after the `if` is not copied into each leaf. -/
def sameFrame (p : Pos) : SExpr := .app p (.ident p "$sameFrame") [] false

def isSameFrame : SExpr → Bool
  | .app _ (.ident _ "$sameFrame") [] false => true
  | _ => false

/-- A hole or a prefix's name, made by `frameOf?` (#283): a name of the
    function's own, which a continuation member has as a parameter. -/
def madeLocal (n : String) : Bool := n.startsWith "$frame" || n.startsWith "$pre"

/-- Literals and the function's own names (`own`: its parameters and
    locals, and the names made for its frames), which read the same after a
    call as before it, since a callee cannot change its caller's names. Not
    a field, which the call may change, nor a constant, which may run code
    where it is read. -/
partial def inert (own : List String) : SExpr → Bool
  | .int .. | .char .. | .char32 .. | .float .. => true
  | .ident _ n => own.contains n || madeLocal n
  | .str _ ps => ps.all fun | .text _ => true | .code _ => false
  | .neg _ e => inert own e
  | .tuple _ es | .arrayLit _ es => es.all (inert own)
  | _ => false

/-- (#283) An alternative with a choice point in it, a call of the recursive
    group or a choice (`isPoint`), and code after it: the first point; the
    alternative with the name `h` in its place, its return frame, which runs
    on each of its values; and the clauses that run before it, once (its
    prefix). What is evaluated before the point is kept in place when it
    reads the same after it (`inert`), else bound to a name in the prefix
    (`$pre…`), so it is still read once, before the point: a field, a
    constant, a call of a function. The code after the point is the frame,
    which may reach another point (a continuation member, `normAlt`). -/
partial def frameOf? (isPoint plain inert : SExpr → Bool) (h : String) (e : SExpr) :
    Option (SExpr × SExpr × List SExpr) :=
  let go := frameOf? isPoint plain inert h
  -- (the operand with the point: those before it bound first unless inert)
  let inList (es : List SExpr) : Option (SExpr × List SExpr × List SExpr) := do
    let i ← es.findIdx? (!plain ·)
    let (c, ei, pre) ← go es[i]!
    let (before, bound) := (es.take i).foldr (fun x (acc, ds) =>
      if inert x then (x :: acc, ds) else
        let t := s!"$pre{x.pos.line}_{x.pos.col}"
        (.ident x.pos t :: acc, .decl x.pos t none false x :: ds)) ([], [])
    return (c, before ++ [ei] ++ es.drop (i + 1), bound ++ pre)
  if isPoint e then some (e, .ident e.pos h, []) else
  match e with
  | .bin p o a b => do
    let (c, as, pre) ← inList [a, b]
    return (c, .bin p o as[0]! as[1]!, pre)
  -- (#283) `A or B` with a point on its right: the `if` it stands for
  | .orE p a b => if plain a && !plain b then
      let t := madeName "or" "" p
      go (.ite p [.decl p t none false (.block a.pos [a])] (.ident p t) (some (.block b.pos [b])))
    else none
  | .neg p a => do let (c, a', pre) ← go a; return (c, .neg p a', pre)
  | .member p a m => do let (c, a', pre) ← go a; return (c, .member p a' m, pre)
  | .cmp p a rest => do
    let (c, a', pre) ← go a
    return (c, .cmp p a' rest, pre)
  | .tuple p es => do let (c, es', pre) ← inList es; return (c, .tuple p es', pre)
  | .arrayLit p es => do let (c, es', pre) ← inList es; return (c, .arrayLit p es', pre)
  | .app p f@(.ident ..) as br => do
    guard (as.all fun | .decl .. => false | _ => true)
    let (c, as', pre) ← inList as
    return (c, .app p f as' br, pre)
  -- (an index, or a call of a value: its head first)
  | .app p f as br => do
    let (c, f', pre) ← go f
    return (c, .app p f' as br, pre)
  | .str p ps => do
    let codes := ps.filterMap fun | .code c => some c | .text _ => none
    let (c, codes', pre) ← inList codes
    let (ps', _) := ps.foldl (fun (acc, rest) part => match part, rest with
      | .code _, x :: xs => (acc ++ [SPart.code x], xs)
      | part, xs => (acc ++ [part], xs)) (([] : List SPart), codes')
    return (c, .str p ps', pre)
  -- (a block: its clauses before the one with the point run before it; its
  -- own `defer:`s after its value, `deferLastBlock`)
  | b@(.block p _) => do
    let ss := stmtsOf (deferLastBlock b)
    let i ← ss.findIdx? (!plain ·)
    let rest := ss.drop (i + 1)
    match ss[i]! with
    | .decl q x t false rhs =>
      let (c, rhs', pre) ← go rhs
      return (c, .block p (.decl q x t false rhs' :: rest), ss.take i ++ pre)
    | s =>
      let (c, s', pre) ← go s
      return (c, .block p (s' :: rest), ss.take i ++ pre)
  | _ => none

/-- (#283) A body whose last choice, or call of the group, is bound by a
    clause with plain code after it, `S; X := a | b; T; v`: the clauses `S`,
    and the choice of `block{X := a; T; v}` and `block{X := b; T; v}`, whose
    calls of the group then have return frames (`normAlt`). -/
def lastChoiceTail (plain : SExpr → Bool) (cls : List SExpr) (last : SExpr) :
    Option (List SExpr × SExpr) := do
  let i ← cls.findIdx? (!plain ·)
  let after := cls.drop (i + 1) ++ [last]
  guard (after.all plain)
  let .decl q x t false rhs := cls[i]! | none
  let alt (a : SExpr) : SExpr := .block a.pos (.decl q x t false a :: after)
  return (cls.take i, match alts? rhs with
    | some as => mk rhs.pos (as.map alt)
    | none => alt rhs)

/-- (#283) A continuation member, the code after a choice point that reaches
    another one, as `normAlt` makes it: `$cont(block{clauses}, tail)`, its
    clauses plain and its tail a generator's, whose alternatives may have
    frames, continuation members again. -/
def contOf? : SExpr → Option (List SExpr × SExpr)
  | .app _ (.ident _ "$cont") [.block _ cls, tail] false => some (cls, tail)
  | _ => none

/-- (#283) How many alternatives `a` is with each choice it has as a choice
    point, `$then(choice, h, frame)`, flattened: one per alternative of the
    choice, each with that frame too, the frame shared. -/
partial def flatCount (a : SExpr) : Nat :=
  match a with
  | .app _ (.ident _ "$then") (c :: _) false => match alts? c, c with
    | some cs, _ => (cs.map flatCount).foldl (· + ·) 0
    -- (an `if`'s leaf with a frame of its own: its count)
    | none, .app _ (.ident _ "$then") _ false => flatCount c
    | none, _ => 1
  | _ => 1

/-- (#283) The holes of the frames in a tail that are continuation members,
    at any depth (theirs too). -/
partial def contHoles (e : SExpr) : List String :=
  (match e with
    | .app _ (.ident _ "$then") (_ :: .ident _ h :: k :: _) false => if (contOf? k).isSome then [h] else []
    | _ => []) ++ e.children.flatMap contHoles

/-- (#283) Whether a tail has a choice point that a plain return frame of a
    call does not cover: a continuation member, a choice with a frame, or
    nested frames which the single-frame machine cannot flatten. -/
def hasContinuation (tail : SExpr) : Bool :=
  anyE (fun
    | .app _ (.ident _ "$cont") _ false => true
    | .app _ (.ident _ "$then") (c :: _) false => isChoice c ||
      (match c with | .app _ (.ident _ "$then") _ false => true | _ => false)
    | _ => false) tail

/-- (#283) An alternative, one of several, with code before a choice in it,
    `$then(choice, h, frame, block{code})`: that code runs after the choice
    the alternative is of, and before its own, so it enters a continuation
    member that runs that code, then its choice, through a hole of no value,
    `$then((), h', $cont(code, $then(choice, h, frame)))`. Alone in its leaf
    it is the leaf's path code instead (`normTail`). -/
def enterOf (a : SExpr) : SExpr := match a with
  | .app q (.ident r "$then") [c, .ident hq h, k, .block _ pre] false =>
    if !isChoice c then a else
    .app q (.ident r "$then") [.tuple q [], .ident hq s!"{h}e",
      .app q (.ident q "$cont") [.block q pre, .app q (.ident r "$then") [c, .ident hq h, k] false] false] false
  | a => a

/-- The tests a lazily taken group's shape is made with (#246, #283): `plain`
    code has no choice and no call of the group or of a function with several
    values; `isRec`, a whole call of the group with plain arguments; `inert`,
    what reads the same after a choice point as before it. -/
structure ShapeOps where
  plain : SExpr → Bool
  isRec : SExpr → Bool
  inert : SExpr → Bool
  /-- A call of the group, whatever its arguments. -/
  isCall : SExpr → Bool := isRec
  /-- A struct's or class's fields in declaration order, for the lifter. -/
  fieldOrder : String → FieldOrder := fun _ => {}
  framePrefix : String := ""

/-- (#283) The calls of a lazily taken group in `e` marked for the lifter,
    `$point(call)`, which binds each where it binds a choice (`liftE`). -/
partial def markPoints (isCall : SExpr → Bool) (e : SExpr) : SExpr :=
  mapE (fun x => if !isCall x then none else match x with
    | .app p f as br => some (.app p (.ident p "$point") [.app p f (as.map (markPoints isCall)) br] false)
    | _ => none) e

/-- The marks of `markPoints` taken off. -/
partial def unmarkPoints : SExpr → SExpr :=
  mapE fun
    | .app _ (.ident _ "$point") [c] false => some (unmarkPoints c)
    | _ => none

/-- (#283) Code whose first choice point `frameOf?` does not reach, lifted as
    the lifter lifts any clause (`liftClause`): its first statement with a
    point, or the code itself as a value, each point bound to a name of its
    own first, as the code evaluates it (a comparison's later operand, a
    `set`'s value, a call's named argument, `and`'s
    operands, `or`'s right, a construction's field in its type's order). None
    when nothing is lifted: the point is where the lifter does not take it
    either (a condition, a loop), which takes it as a failure context's. -/
def liftPoints? (ops : ShapeOps) (a : SExpr) : Option SExpr := do
  let isVal (n : String) : Bool := ops.inert (.ident a.pos n)
  -- (an `if` with a point in a branch the lifter binds as an exclusive
  -- choice is bound as itself, a point of the normal form, `ifPoint`)
  let whole : SExpr → SExpr
    | .decl p x ty false (.app _ (.ident _ "$branchChoice") [i] false)
    | .decl p x ty false (.app _ (.ident _ "$branchChoiceAt") [_, i] false) => .decl p x ty false i
    | c => c
  -- (a `set`'s or a `var`'s value that is a choice with a point in an
  -- alternative bound first, as `normClauses` binds a choice: after the
  -- path's prefix)
  let lift (c : SExpr) : List SExpr :=
    (normClauses (liftClause isVal (fun _ _ => false) (markPoints ops.isCall c) (fieldOrder := ops.fieldOrder))).map
      (whole ∘ unmarkPoints)
  -- (none where the lifter keeps something, `$noLift`: a construction
  -- whose fields' order it does not know, as a class's, where the function
  -- is then not of the shape, as before)
  let kept (cs : List SExpr) : Bool :=
    cs.any (anyE fun | .app _ (.ident _ "$noLift") _ false => true | _ => false)
  match a with
  | .block p ss =>
    let i ← ss.findIdx? (!ops.plain ·)
    let lifted := lift ss[i]!
    guard (lifted.length > 1 && !kept lifted)
    return .block p (ss.take i ++ lifted ++ ss.drop (i + 1))
  | e =>
    let v := madeName "lv" "" e.pos
    let lifted := lift (.decl e.pos v none false e)
    guard (lifted.length > 1 && !kept lifted)
    return .block e.pos (lifted ++ [.ident e.pos v])

mutual
/-- (#283) An alternative of a lazily taken group in the normal form its
    machine takes: a plain value; a whole call of the group; or a choice
    point, a call of the group or a choice, with the code after it, its return
    frame (`frameOf?`): `$then(point, hole, frame)`, with the clauses that
    run before the point when there are any, `$then(point, hole, frame,
    block{prefix})`. A choice's alternatives are in this form again, and the
    frame is plain code, or a continuation member (`contBody?M`) when it
    reaches another choice point: so each choice point and each call is the
    head of the code after it. The hole of a frame of a call with plain code
    after it is named as #283's first frames were, after the alternative;
    others after the point and its kind. -/
partial def normAltM (ops : ShapeOps) (a : SExpr) : StateT Nat Option SExpr := do
  if ops.isRec a then return a
  -- (a value: its `if`s with a `return` in a branch plain ones again, as an
  -- eager body's, #283; a tail's own scope stays the tail's)
  if ops.plain a then return (match a with
    | .app _ (.ident _ "$returnTail") _ false => a
    | a => eraseReturnTails a)
  -- (a block taken apart: its own `defer:`s after its value, as the lifter
  -- places them, so they run as each value leaves it)
  let a := deferLastBlock a
  -- (a block that starts with a choice bound, with plain code after it: the
  -- choice of that code after each alternative, as `lastChoiceTail`)
  if let .block _ ss@(_ :: _ :: _) := a then
    if let some ([], tail) := lastChoiceTail ops.plain ss.dropLast ss.getLast! then
      -- (one of them with code before a choice of its own enters a member
      -- that runs it, `enterOf`, as anywhere a choice's alternatives are)
      if let some as := alts? tail then return mk a.pos ((← as.mapM (normAltM ops)).map enterOf)
  -- (#283) an `if` with plain conditions and a point in a branch is one too:
  -- its branch's values go to the code after it
  let ifPoint : SExpr → Bool
    | e@(.ite _ cs _ (some _)) => cs.all ops.plain && !ops.plain e
    | _ => false
  let isPoint (e : SExpr) : Bool := ops.isRec e || isChoice e || ifPoint e
  let hole := "$hole"
  match frameOf? isPoint ops.plain ops.inert hole a with
  | none =>
    -- (a point `frameOf?` does not reach, but the lifter does: lifted)
    let a' ← liftPoints? ops a
    normAltM ops a'
  | some (c, k, pre) => do
    guard (pre.all ops.plain)
    let pre := pre.map eraseReturnTails
    let serial ← get
    modify (· + 1)
    let h := (if ops.isRec c && ops.plain k then s!"$frame{a.pos.line}_{a.pos.col}"
      else s!"$frame{c.pos.line}_{c.pos.col}{if ops.isRec c then "k" else if ifPoint c then "i" else "c"}") ++ s!"${ops.framePrefix}_{serial}"
    let k := renameE [(hole, h)] k
    -- (a frame that reaches no other point: plain code, its `if`s with a
    -- `return` in a branch plain ones again, as an eager body's, #283)
    let plainFrame (k : SExpr) : SExpr := eraseReturnTails k
    if ifPoint c then
      -- (an `if`: entered as `enterOf` enters a member, its conditions the
      -- member's path, each leaf's values going to the frame, one for all,
      -- its code in the first leaf only, `sameFrame`)
      let k ← if ops.plain k then pure (plainFrame k) else contBody?M ops k
      let tail := mapLoopLeavesIdx (fun i v => .app v.pos (.ident v.pos "$then")
        [v, .ident v.pos h, if i == 0 then k else sameFrame v.pos] false) (← normTailM ops c)
      let q := a.pos
      return .app q (.ident q "$then") [.tuple q [], .ident q s!"{h}e",
        .app q (.ident q "$cont") [.block q pre, tail] false] false
    let c ← match alts? c with
      | some cs => do
        -- (one of its alternatives with code before a choice of its own
        -- enters a member that runs it, `enterOf`)
        let cs ← cs.mapM (normAltM ops)
        pure (mk c.pos (cs.map enterOf))
      | none => pure c
    let k ← if ops.plain k then pure (plainFrame k) else contBody?M ops k
    let q := a.pos
    return .app q (.ident q "$then") ([c, .ident q h, k] ++ (if pre.isEmpty then [] else [.block q pre])) false

/-- (#283) A tail's leaves in normal form (`normAltM`). A leaf that is one
    choice with a prefix, `$then(choice, h, frame, block{prefix})`, has the
    prefix run as its path's, before the choice. -/
partial def normTailM (ops : ShapeOps) (tail : SExpr) : StateT Nat Option SExpr :=
  match tail with
  | .app p (.ident q "$returnTail") [.block r ss] false => do
    let (pre, value) := loopBlockParts r ss
    if pre.all ops.plain then
      return .app p (.ident q "$returnTail") [.block r (pre.map eraseReturnTails ++ [← normTailM ops value])] false
    -- (a returning branch whose code before its value has choice points: as
    -- a body, its code up to the first its path's)
    let (cls, t) ← bodyTail?M ops r pre value
    return .app p (.ident q "$returnTail") [.block r (cls ++ [t])] false
  | .ite p cs t u => do return .ite p cs (← normTailM ops t) (← u.mapM (normTailM ops))
  | v => do
    match alts? v with
    | some as => return mk v.pos ((← as.mapM (normAltM ops)).map enterOf)
    | none =>
      match ← normAltM ops v with
      | a@(.app q (.ident _ "$then") [.tuple _ [], .ident _ hole,
          .app _ (.ident _ "$cont") [.block _ pre, tail] false] false) =>
        -- At a member's own tail there is no surrounding alternative to
        -- enter. Keep its path prefix and selection, without an unused
        -- void-return frame and its slot in every continuation tuple.
        if pre.all ops.plain && !(namesUsed (.block q (pre ++ [tail]))).contains hole then
          if pre.isEmpty then return tail
          return .app q (.ident q "$returnTail") [.block q (pre ++ [tail])] false
        return a
      | .app q (.ident r "$then") [c, h, k, .block _ pre] false =>
        if isChoice c then
          return .app q (.ident r "$returnTail") [.block q (pre ++ [.app q (.ident r "$then") [c, h, k] false])] false
        normAltM ops v
      | a => return a

/-- (#283) The clauses and tail of code whose clauses `cls` are followed by
    `last`: the clauses up to the first that is not plain, and the rest as
    the tail. A last choice bound with plain code after it is the choice of
    that code after each alternative (`lastChoiceTail`); otherwise what comes
    from the first choice point on is one alternative (`normAltM`). -/
partial def bodyTail?M (ops : ShapeOps) (p : Pos) (cls : List SExpr) (last : SExpr) :
    StateT Nat Option (List SExpr × SExpr) := do
  let leafOf (cls : List SExpr) (tail : SExpr) : StateT Nat Option (List SExpr × SExpr) := do
    guard (cls.all ops.plain)
    return (cls.map eraseReturnTails, ← normTailM ops (plainIfValues ops.plain (completeLoopTail ops.isRec false tail)))
  if cls.all ops.plain then
    leafOf cls (match last with | .decl _ _ _ false rhs => rhs | e => e)
  else match lastChoiceTail ops.plain cls last with
    | some (cls, tail) => leafOf cls tail
    | none =>
      let i ← cls.findIdx? (!ops.plain ·)
      return (cls.take i, ← normTailM ops (.block p (cls.drop i ++ [last])))

/-- (#283) The frame `k` that reaches another choice point as a continuation
    member, `$cont(block{clauses}, tail)` (`bodyTail?M`). -/
partial def contBody?M (ops : ShapeOps) (k : SExpr) : StateT Nat Option SExpr := do
  let ss := stmtsOf k
  let last ← ss.getLast?
  let (cls, tail) ← bodyTail?M ops k.pos ss.dropLast last
  return .app k.pos (.ident k.pos "$cont") [.block k.pos cls, tail] false
end

def normAlt (ops : ShapeOps) (a : SExpr) : Option SExpr := (normAltM ops a).run' 0
def normTail (ops : ShapeOps) (tail : SExpr) : Option SExpr := (normTailM ops tail).run' 0
def bodyTail? (ops : ShapeOps) (p : Pos) (cls : List SExpr) (last : SExpr) : Option (List SExpr × SExpr) :=
  (bodyTail?M ops p cls last).run' 0
def contBody? (ops : ShapeOps) (k : SExpr) : Option SExpr := (contBody?M ops k).run' 0

/-- Why a recursive function with several values whose values are computed
    at the call must be effect-free, and when it is taken lazily instead. -/
def eagerWhy : String :=
  "such a function must be <computes>, keep no local state, and reach nothing that prints or calls Err(), " ++
  "as all its values are computed at a call (#235), unless it is taken lazily: clauses, then a choice whose " ++
  "alternatives are values or calls of functions with several values (its group's, or others it calls, taken " ++
  "with it), or such a call or a choice with code after it that may reach another (#246, #283)"

/-- (#283) Whether an alternative in normal form (`normAlt`) is one the
    lazy machine takes: its prefix plain, a choice's alternatives such again,
    and its frame plain or a continuation member whose clauses are plain and
    whose tail's leaves are such. A frame sets no `var` bound before it
    (`isVar`), as it runs on a copy of the names it uses (an object's field
    it may set). -/
partial def altOK (ops : ShapeOps) (isVar : String → Bool) (a : SExpr) : Bool :=
  ops.isRec a || ops.plain a || match a with
    | .app _ (.ident _ "$then") (c :: _ :: k :: pre) false =>
      let leafOK (e : SExpr) : Bool := ((alts? e).getD [e]).all (altOK ops isVar)
      -- (a choice with code before it is a whole leaf, that code its path's,
      -- `normTail`; not yet one alternative among others)
      (pre.isEmpty || !isChoice c) &&
      pre.all ops.plain && ((alts? c).map (·.all (altOK ops isVar))).getD
        (ops.isRec c || ops.plain c || (match c with | .app _ (.ident _ "$then") _ false => altOK ops isVar c | _ => false)) &&
        (setsIn k).all (fun n => (localsOf k).contains n || !isVar n) &&
        (ops.plain k || match contOf? k with
          | some (cls, tail) => cls.all ops.plain && loopTailOK ops.plain leafOK tail
          | none => false)
    | _ => false

/-- The shape of a recursive function with several values that its
    consumers take lazily (#246), after normalizing source returns: plain
    clauses and conditional tail paths, each leaf a choice or value whose
    alternatives are whole calls of the recursive group or plain values.
    With `frames` (#283), the body in the normal form of `normAlt`: an
    alternative may also be a choice point (a call of the group, or a choice)
    with code after it, which runs on each of its values (`$then`), and the
    clauses may end at a choice point with code after it (`bodyTail?`). -/
def loopShapeOf? (g : String) (mv : List String) (body : SExpr) (grp : List String := [g])
    (frames : Bool := false) (params : List String := [])
    (fieldOrder : String → FieldOrder := fun _ => {}) : Option (List SExpr × SExpr) := do
  let ss := stmtsOf body
  let last ← ss.getLast?
  let cls := ss.dropLast
  -- (no choice, and no call of a function with several values, nor any
  -- other mention of `g`: a call of it its own `if` or `for` takes, say)
  -- (#283: or of a function of its strongly connected group, `grp`)
  let plain (e : SExpr) : Bool := !liftsHere (markCalls mv (eraseReturnTails e)) && !(namesUsed e).any grp.contains
  let isRec : SExpr → Bool
    | .app _ (.ident _ h) as _ => grp.contains h && as.all fun a =>
        match a with
        | .decl _ n _ _ rhs => n.startsWith "?" && plain rhs
        | _ => plain a
    | _ => false
  if !frames then
    let tail := match last with
      | .decl _ _ _ false rhs => rhs
      | e => e
    let tail := plainIfValues plain (completeLoopTail isRec false tail)
    let groupOK (e : SExpr) : Bool := ((alts? e).getD [e]).all fun a => isRec a || plain a
    if cls.all plain && loopTailOK plain groupOK tail then some (cls, tail) else none
  else
  let isCall : SExpr → Bool
    | .app _ (.ident _ h) _ _ => grp.contains h
    | _ => false
  let ops : ShapeOps := { plain, isRec, inert := inert (params ++ localsOf body), isCall, fieldOrder, framePrefix := sitePart g }
  let (cls, tail) ← bodyTail? ops body.pos cls last
  let isVar (n : String) : Bool := anyE (fun | .decl _ x _ true _ => x == n | _ => false) body
  let groupOK (e : SExpr) : Bool := ((alts? e).getD [e]).all (altOK ops isVar)
  if cls.all plain && loopTailOK plain groupOK tail then some (cls, tail) else none

/-- (#283) A function's `var`s made cells: `var K:t = e` becomes
    `K := $varcell(t){$VCell := e}`, and each use of `K`, read or `set`, is
    `K.$VCell`. A return frame runs on a copy of the names it uses, but a
    cell is one object: what a value's frame sets, every later value of the
    call and every later alternative sees, and a rejected value's write is
    undone with it, as the inlined body's `var` would be. -/
partial def cellVars (vs : List String) : SExpr → SExpr :=
  mapE fun
    | .decl p x (some t) true rhs =>
      if vs.contains x then
        some (.decl p x none false (.construct p "$varcell" [t] [.decl p "$VCell" none false (cellVars vs rhs)]))
      else none
    | .ident p x => if vs.contains x then some (.member p (.ident p x) "$VCell") else none
    | _ => none

/-- `loopShapeOf?`; with `frames`, when a frame sets a `var` (#283), with the
    function's `var`s that are set made cells (`cellVars`). -/
def loopShape? (g : String) (mv : List String) (body : SExpr) (grp : List String := [g])
    (frames : Bool := false) (params : List String := [])
    (fieldOrder : String → FieldOrder := fun _ => {}) : Option (List SExpr × SExpr) :=
  (loopShapeOf? g mv body grp frames params fieldOrder).orElse fun _ =>
    let set := setsIn body
    let vs := ((localDecls body).map (·.1)).eraseDups.filter fun x =>
      set.contains x && anyE (fun | .decl _ y (some _) true _ => y == x | _ => false) body
    if !frames || vs.isEmpty then none else loopShapeOf? g mv (cellVars vs body) grp frames params fieldOrder

/-- How many `if`s with a `return` in them `e` has (#283), a `case`'s arms
    counted as the `if` chain that selects them (`caseIf`). -/
partial def countRetIfs (e : SExpr) : Nat :=
  let sum (ss : List SExpr) : Nat := (ss.map countRetIfs).foldl (· + ·) 0
  match e with
  | .ite _ cs t u? =>
    (if hasReturn t || u?.any hasReturn then 1 else 0) + sum cs + sum (stmtsOf t) + ((u?.map (sum ∘ stmtsOf)).getD 0)
  | .block _ ss => sum ss
  | .caseE _ _ arms =>
    (if arms.any (hasReturn ·.2) then arms.length - 1 else 0) + sum (arms.flatMap (stmtsOf ·.2))
  | _ => 0

/-- The statements `ss` with their last value returned (#283): the value of
    a body that ends in an `if` with a `return` in it is its branches'. -/
partial def tailReturns (ss : List SExpr) : List SExpr :=
  match ss.getLast? with
  | none => ss
  | some last =>
    let init := ss.dropLast
    match last with
    | .ret .. => ss
    | .decl q x _ _ _ => ss ++ [.ret q (some (.ident q x))]
    | .ite q cs t u? =>
      init ++ [.ite q cs (.block q (tailReturns (stmtsOf t))) (u?.map fun u => .block q (tailReturns (stmtsOf u)))]
    -- (#283) a block, or a `case`, with a `return` in it: its value, or its
    -- arms', returned in it, so that it is a scope taken out as a branch is
    | .block q bs => if hasReturn last then init ++ [.block q (tailReturns bs)] else init ++ [.ret q (some last)]
    | .caseE q e arms =>
      if !arms.any (hasReturn ·.2) then init ++ [.ret q (some last)] else
      init ++ [.caseE q e (arms.map fun (pat, a) => (pat, .block a.pos (tailReturns (stmtsOf a))))]
    | e => if isDefer e then ss ++ [.ret e.pos none] else init ++ [.ret e.pos (some e)]

/-- A normalized returning conditional: branch selection adds no generator
    boundary; only a branch's own choices generate values. -/
def returnBranches (p : Pos) (k : String) (cs tb ub : List SExpr)
    (multi : SExpr → Bool) (ret : Option STy) (tailBlocks : Bool := false) : List SExpr :=
  if tailBlocks || (!multi (.block p tb) && !multi (.block p ub)) then
    let scope (ss : List SExpr) := if tailBlocks then
      SExpr.app p (.ident p "$returnTail") [.block p ss] false else .block p ss
    [.ite p cs (scope tb) (some (scope ub))]
  else
  -- (a branch with a choice of its own: an exclusive choice of the two,
  -- which a `for` compiles as this `if`, #314; the condition once)
  let v := k ++ "v"
  let (sel, excl) := exclOfIf p k cs (.block p tb) (.block p ub)
  [sel, .decl p v ret false excl, .ident p v]

/-- The names of a branch that a `return` is taken out of, renamed for it
    (`tag'N`): its statements' locals and `extra` (its condition's), so the
    rest of the body copied into it may declare the same ones (#283). -/
def branchNames (tag : String) (ss : List SExpr) (extra : List String) : List (String × String) :=
  renamedFor tag ((ss.flatMap localsOf) ++ extra).eraseDups

/-- A body's statements with its `return`s, in `if`s, taken out (#283):
    an `if` with a `return` in a branch, `S; if (C) { T } else { U }; R`,
    becomes the value `S; if (C) then block{ T; R } else block{ U; R }`, a
    `return v` ending its block with the value `v` (so the rest is left out
    after a branch that always returns). When a branch has a choice of its
    own (`multi`), it is an exclusive choice of the two instead (#314),
    `$k := if (C) then 0 else 1; $kv := $excl(($k = 0) ⇒ T; R, ($k = 1) ⇒ U; R)`
    (a condition that binds names through an option), which a `for`
    compiles as the `if` it stands for: no generator, so what came before
    it rolls back as without the return. A branch's own names, and its
    condition's, are renamed for it (`fresh i ++ "'" ++ N`), so the rest
    copied into it may declare the same ones. `none` when a `return` is
    elsewhere (in a loop, a condition, an expression). -/
partial def elimPlainReturns (fresh : Nat → String) (n : Nat) (multi : SExpr → Bool := fun _ => false)
    (ret : Option STy) (tailBlocks : Bool) : List SExpr → Option (List SExpr × Nat)
  | [] => some ([], n)
  | .ret p e? :: _ => some ([e?.getD (.tuple p [])], n)
  | s@(.ite p cs t u?) :: rest =>
    if !hasReturn s then (elimPlainReturns fresh n multi ret tailBlocks rest).map fun (r, n') => (s :: r, n')
    else if cs.any hasReturn then none
    else do
      let k := fresh n
      -- (the last statement of a body: its branches' values are returned)
      let (ts, us) := if rest.isEmpty then
          (tailReturns (stmtsOf t), tailReturns ((u?.map stmtsOf).getD []))
        else (stmtsOf t, (u?.map stmtsOf).getD [])
      -- (a branch's names, and its condition's, are its own)
      let ρt := branchNames s!"{k}t" ts (boundIn cs)
      let ρu := branchNames s!"{k}u" us []
      let ts := ts.map (renameE ρt)
      let us := us.map (renameE ρu)
      let (tb, n1) ← elimPlainReturns fresh (n + 1) multi ret tailBlocks (ts ++ rest)
      let (ub, n2) ← elimPlainReturns fresh n1 multi ret tailBlocks (us ++ rest)
      let cs := cs.map (renameE ρt)
      some (returnBranches p k cs tb ub multi ret tailBlocks, n2)
  -- (#283) a block with a `return` in it, a scope of its own: its statements
  -- in its place, its names renamed for it, as an `if`'s branch's are
  | s@(.block _ bs) :: rest =>
    if !hasReturn s then (elimPlainReturns fresh n multi ret tailBlocks rest).map fun (r, n') => (s :: r, n')
    else elimPlainReturns fresh (n + 1) multi ret tailBlocks
      (bs.map (renameE (branchNames s!"{fresh n}b" bs [])) ++ rest)
  -- (#283) a `case` with a `return` in an arm: the `if` chain it selects with
  | s@(.caseE ..) :: rest =>
    if !hasReturn s then (elimPlainReturns fresh n multi ret tailBlocks rest).map fun (r, n') => (s :: r, n')
    else do
      let (sel, chain) ← caseIf (fresh n) s
      elimPlainReturns fresh (n + 1) multi ret tailBlocks (sel :: chain :: rest)
  | s :: rest =>
    if hasReturn s then none
    else (elimPlainReturns fresh n multi ret tailBlocks rest).map fun (r, n') => (s :: r, n')

/-- The surrounding scope's fallthrough code and currently registered
    cleanup, retained while normalizing an inner returning branch. -/
structure ReturnScope where
  pos : Pos
  rest : List SExpr
  defers : List SExpr

/-- Execute one scope's reached registrations, last registered first. -/
def runReturnDefers : List SExpr → List SExpr
  | [] => []
  | d :: ds => [.block d.pos (d :: ds ++ [.int d.pos 0])]

/-- Normalize returns without moving cleanup across a lexical scope or an
    earlier return path. Fallthrough unwinds this scope before resuming the
    parent's continuation; a return saves its operand and unwinds every
    active scope before yielding the saved value. -/
partial def elimScopedReturns (fresh : Nat → String) (multi : SExpr → Bool) (ret : Option STy)
    (n : Nat) (p : Pos) (ss ds : List SExpr) (outer : List ReturnScope) : Option (List SExpr × Nat) :=
  match ss with
  | [] => do
    match outer with
    | [] => some (runReturnDefers ds ++ [.tuple p []], n)
    | scope :: parents =>
      let (rest, n') ← elimScopedReturns fresh multi ret n scope.pos scope.rest scope.defers parents
      some (runReturnDefers ds ++ rest, n')
  | .ret q value :: _ =>
    let cleanup := runReturnDefers ds ++ outer.flatMap fun scope => runReturnDefers scope.defers
    let value := value.getD (.tuple q [])
    if cleanup.isEmpty then some ([value], n) else
    let saved := fresh n ++ "$value"
    some (.decl q saved ret false value :: cleanup ++ [.ident q saved], n + 1)
  | d@(.app _ (.ident _ "$defer") _ _) :: rest =>
    -- A moved registration still cannot see declarations after it.
    let later := renamedFor "$later" (boundIn rest)
    elimScopedReturns fresh multi ret n p rest (ds ++ [renameE later d]) outer
  | s@(.ite q cs t u?) :: rest => do
    if !hasReturn s then
      let (rest, n') ← elimScopedReturns fresh multi ret n p rest ds outer
      some (s :: rest, n')
    else if cs.any hasReturn then none else
      let k := fresh n
      let ts := stmtsOf t
      let us := (u?.map stmtsOf).getD []
      let ρt := branchNames s!"{k}t" ts (boundIn cs)
      let ρu := branchNames s!"{k}u" us []
      let parents := { pos := p, rest, defers := ds } :: outer
      let (tb, n1) ← elimScopedReturns fresh multi ret (n + 1) t.pos (ts.map (renameE ρt)) [] parents
      let (ub, n2) ← elimScopedReturns fresh multi ret n1 q (us.map (renameE ρu)) [] parents
      some (returnBranches q k (cs.map (renameE ρt)) tb ub multi ret, n2)
  -- (#283) a block with a `return` in it: a scope inside this one, as an
  -- `if`'s branch is, its names renamed for it
  | s@(.block q bs) :: rest => do
    if !hasReturn s then
      let (rest, n') ← elimScopedReturns fresh multi ret n p rest ds outer
      some (s :: rest, n')
    else
      let parents := { pos := p, rest, defers := ds } :: outer
      elimScopedReturns fresh multi ret (n + 1) q (bs.map (renameE (branchNames s!"{fresh n}b" bs []))) [] parents
  -- (#283) a `case` with a `return` in an arm: the `if` chain it selects with
  | s@(.caseE ..) :: rest => do
    if !hasReturn s then
      let (rest, n') ← elimScopedReturns fresh multi ret n p rest ds outer
      some (s :: rest, n')
    else
      let (sel, chain) ← caseIf (fresh n) s
      elimScopedReturns fresh multi ret (n + 1) p (sel :: chain :: rest) ds outer
  | s :: rest => do
    if hasReturn s then none else
      let (rest, n') ← elimScopedReturns fresh multi ret n p rest ds outer
      some (s :: rest, n')

private def linearReturnFinish (fresh : Nat → String) (p : Pos) (ret : STy) (n : Nat) (outcome : Bool)
    (value : SExpr) (cleanup : List SExpr) : List SExpr × Nat :=
  if !outcome && cleanup.isEmpty then ([value], n) else
  let saved := fresh n ++ "$returnValue"
  let result := if outcome then SExpr.optionLit p (.block p [.ident p saved]) else .ident p saved
  (.decl p saved (some ret) false value :: cleanup ++ [result], n+1)

/-- Only scalar expressions cross this private boundary. Choices that need
    a lazy return-operand continuation retain the existing refusal. -/
private partial def scalarReturnBoundary (many : SExpr → Bool) (e : SExpr) : Bool :=
  !many e && match e with
  | .app _ (.ident _ name) _ _ =>
    !["$sync", "$race", "$rush", "$branch", "$spawn"].contains name &&
      e.children.all (scalarReturnBoundary many)
  | .ret _ value => value.all fun value => !many value && scalarReturnBoundary many value
  | _ => e.children.all (scalarReturnBoundary many)

/-- Ordinary conditions cannot expose a selected binding or a refinement
    world to the statements after an initializer. Keep those cases in the
    original expression boundary rather than moving their continuation. -/
private partial def plainReturnCondition : SExpr → Bool
  | .int .. | .char .. | .char32 .. | .float .. | .ident .. => true
  | .member _ value _ | .query _ value | .neg _ value | .notE _ value =>
    plainReturnCondition value
  | .bin _ _ left right | .andE _ left right | .orE _ left right =>
    plainReturnCondition left && plainReturnCondition right
  | .cmp _ first rest => plainReturnCondition first && rest.all (plainReturnCondition ·.2)
  | _ => false

/-- With one direct scalar return and one normal arm, only the normal arm
    reaches the binding and its suffix. Its value block remains the binding's
    RHS, so its own cleanup still finishes before that suffix starts. -/
def splitReturnInitializer (many : SExpr → Bool) (q : Pos) (name : String)
    (ty : Option STy) (mutable : Bool) (body : SExpr) (rest : List SExpr) :
    Option (List SExpr) := do
  let .ite p conditions yes (some no) := body | none
  guard (conditions.all plainReturnCondition)
  let branch (arm : SExpr) : Option (List SExpr) :=
    match arm with
    | .ret .. => if scalarReturnBoundary many arm then some [arm] else none
    | _ => if hasReturn arm then none else some (.decl q name ty mutable arm :: rest)
  let oneReturn : Bool := match yes, no with
    | .ret .., .ret .. => false
    | .ret .., _ | _, .ret .. => true
    | _, _ => false
  guard oneReturn
  let yes ← branch yes
  let no ← branch no
  return declNames q [(name, q)] ++ [.ite p conditions (.block p yes) (some (.block p no))]

def returnBoundary (p : Pos) (key : String) (ret : STy)
    (normal : Option STy) (body : SExpr) : SExpr :=
  -- Only outer mutations are part of the caller's copy-out contract.
  -- Names owned by the scalar expression stay private to that expression.
  let owned := localsOf body
  let writes := (setsIn body).eraseDups.filterMap fun name =>
    if owned.contains name then none
    else some (SExpr.set p (.ident p name) none (.ident p name))
  .app p (.ident p "$returnBoundary")
    [.block p writes, .decl p (key ++ "Type") (some ret) false (.tuple p []),
     .decl p (key ++ "Body") normal false body] false

private def returnChoices (body : SExpr) : Bool :=
  hasChoice (stmtsOf body) || (stmtsOf body).any liftsHere

private def linearReturnResume (p : Pos) (key : String) (ret : STy) (outcome : Bool)
    (returned rest : List SExpr) (branchMany : SExpr → Bool := returnChoices) (tailBlocks : Bool := false) : List SExpr :=
  let payload := key ++ "Value"
  returnBranches p (key ++ "Select")
    [.decl p payload (some ret) false (.query p (.ident p key))]
    returned rest branchMany
    (some (if outcome then .opt ret else ret)) tailBlocks

private def linearReturnCleanup (outcome : Bool) (defers : List SExpr)
    (outer : List (List SExpr)) : List SExpr :=
  runReturnDefers defers ++ if outcome then [] else outer.flatMap runReturnDefers

/-- A branch produces either a returned value or fallthrough. Its caller
    contains the following source statements once, outside both branches. -/
partial def elimLinearReturns (fresh : Nat → String) (ret : STy) (outcome : Bool) (n : Nat) (p : Pos)
    (ss defers : List SExpr) (outer : List (List SExpr) := [])
    (many : SExpr → Bool := hasLiftable) (branchMany : SExpr → Bool := returnChoices) (tailBlocks : Bool := false) :
    Option (List SExpr × Nat) := do
  match ss with
  | [] => return (linearReturnCleanup outcome defers outer ++
      [if outcome then .ident p "false" else .tuple p []], n)
  | .ret q value :: _ =>
    return linearReturnFinish fresh q ret n outcome (value.getD (.tuple q []))
      (linearReturnCleanup outcome defers outer)
  | d@(.app _ (.ident _ "$defer") _ _) :: rest =>
    let later := renamedFor "$later" (boundIn rest)
    elimLinearReturns fresh ret outcome n p rest (defers ++ [renameE later d]) outer many branchMany tailBlocks
  | s@(.decl q name ty mutable body) :: rest =>
    if !hasReturn body then
      let (tail, next) ← elimLinearReturns fresh ret outcome n p rest defers outer many branchMany tailBlocks
      return (s :: tail, next)
    if !scalarReturnBoundary many body then
      let moved ← splitReturnInitializer many q name ty mutable body rest
      elimLinearReturns fresh ret outcome n p moved defers outer many branchMany tailBlocks
    else do
      let packet := fresh n ++ "$boundary"
      let key := packet ++ "Return"
      let (rest, n1) ← elimLinearReturns fresh ret outcome (n+1) p rest defers outer many branchMany tailBlocks
      -- The normal outcome is present whenever the return outcome is absent.
      -- Keep the binding in this continuation's prefix, rather than adding
      -- another conditional frame that can lose its inferred result type.
      let ready := .decl q name ty mutable
        (.query q (.app q (.ident q packet) [.int q 1] false)) :: rest
      let payload := key ++ "Value"
      let (returned, n2) := linearReturnFinish fresh q ret n1 outcome (.ident q payload)
        (linearReturnCleanup outcome defers outer)
      return (.decl q packet none false (returnBoundary q packet ret ty body) ::
        .decl q key (some (.opt ret)) false (.app q (.ident q packet) [.int q 0] false) ::
        linearReturnResume q key ret outcome returned ready branchMany tailBlocks, n2)
  | s@(.forE q ..) :: rest | s@(.loop q _) :: rest =>
    if !hasReturn s then
      let (tail, next) ← elimLinearReturns fresh ret outcome n p rest defers outer many branchMany tailBlocks
      return (s :: tail, next)
    if !scalarReturnBoundary many s then none else do
      let packet := fresh n ++ "$boundary"
      let key := packet ++ "Return"
      let (rest, n1) ← elimLinearReturns fresh ret outcome (n+1) p rest defers outer many branchMany tailBlocks
      let payload := key ++ "Value"
      let (returned, n2) := linearReturnFinish fresh q ret n1 outcome (.ident q payload)
        (linearReturnCleanup outcome defers outer)
      return (.decl q packet none false (returnBoundary q packet ret none s) ::
        .decl q key (some (.opt ret)) false (.app q (.ident q packet) [.int q 0] false) ::
        linearReturnResume q key ret outcome returned rest branchMany tailBlocks, n2)
  | s@(.ite q cs t u) :: rest =>
    if !hasReturn s then
      let (tail, next) ← elimLinearReturns fresh ret outcome n p rest defers outer many branchMany tailBlocks
      return (s :: tail, next)
    if cs.any hasReturn then none else do
      let key := fresh n ++ "$return"
      if !outcome && rest.isEmpty then
        let (tb, n1) ← elimLinearReturns fresh ret false (n+1) t.pos
          (tailReturns (stmtsOf t)) [] (defers :: outer) many branchMany tailBlocks
        let (ub, n2) ← elimLinearReturns fresh ret false n1 q
          (tailReturns ((u.map stmtsOf).getD [])) [] (defers :: outer) many branchMany tailBlocks
        return (returnBranches q key cs tb ub
          branchMany (some ret) tailBlocks, n2)
      let (tb, n1) ← elimLinearReturns fresh ret true (n+1) t.pos (stmtsOf t) [] outer many branchMany tailBlocks
      let (ub, n2) ← elimLinearReturns fresh ret true n1 q ((u.map stmtsOf).getD []) [] outer many branchMany tailBlocks
      let (rest, n3) ← elimLinearReturns fresh ret outcome n2 p rest defers outer many branchMany tailBlocks
      let payload := key ++ "Value"
      let (returned, n4) := linearReturnFinish fresh q ret n3 outcome (.ident q payload)
        (linearReturnCleanup outcome defers outer)
      let packet := SExpr.ite q cs (.block t.pos tb) (some (.block q ub))
      return (.decl q key (some (.opt ret)) false packet ::
        linearReturnResume q key ret outcome returned rest branchMany tailBlocks, n4)
  | s@(.block q items) :: rest =>
    if !hasReturn s then
      let (tail, next) ← elimLinearReturns fresh ret outcome n p rest defers outer many branchMany tailBlocks
      return (s :: tail, next)
    if !outcome && rest.isEmpty then
      elimLinearReturns fresh ret false (n+1) q (tailReturns items) [] (defers :: outer) many branchMany tailBlocks
    else do
    let key := fresh n ++ "$return"
    let (items, n1) ← elimLinearReturns fresh ret true (n+1) q items [] outer many branchMany tailBlocks
    let (rest, n2) ← elimLinearReturns fresh ret outcome n1 p rest defers outer many branchMany tailBlocks
    let payload := key ++ "Value"
    let (returned, n3) := linearReturnFinish fresh q ret n2 outcome (.ident q payload)
      (linearReturnCleanup outcome defers outer)
    return (.decl q key (some (.opt ret)) false (.block q items) ::
      linearReturnResume q key ret outcome returned rest branchMany tailBlocks, n3)
  | s@(.caseE ..) :: rest =>
    if !hasReturn s then
      let (tail, next) ← elimLinearReturns fresh ret outcome n p rest defers outer many branchMany tailBlocks
      return (s :: tail, next)
    let (select, chain) ← caseIf (fresh n ++ "$returnCase") s
    elimLinearReturns fresh ret outcome (n+1) p (select :: chain :: rest) defers outer many branchMany tailBlocks
  | s :: rest =>
    if hasReturn s then none else do
      let (tail, next) ← elimLinearReturns fresh ret outcome n p rest defers outer many branchMany tailBlocks
      return (s :: tail, next)

/-- Consecutive statements without escaping bindings or cleanup registrations
    in their own scope can share balanced block scopes. Branch and block cleanup
    already belongs to a nested scope, so wrapping those statements preserves it.
    This keeps a large return prefix from becoming a linear-depth nest of collection loops after choice lowering. -/
private partial def balanceReturnRun (ss : List SExpr) : List SExpr :=
  if ss.length ≤ 4 || !ss.any hasReturn then ss else
  let middle := ss.length / 2
  let left := balanceReturnRun (ss.take middle)
  let right := balanceReturnRun (ss.drop middle)
  [.block (left.head?.map (·.pos) |>.getD default) left,
   .block (right.head?.map (·.pos) |>.getD default) right]

private partial def balanceReturnSequence (ss : List SExpr) : List SExpr :=
  let run := ss.takeWhile fun s => (boundIn [s]).isEmpty &&
    (match s with
    | .ite _ cs _ _ => !cs.any (anyE isDefer)
    | .block .. => true
    | .caseE _ selector _ => !anyE isDefer selector
    | _ => !anyE isDefer s) &&
    match s with
    | .app _ (.ident _ name) _ _ => !name.startsWith "$"
    | _ => true
  let rest := ss.drop run.length
  balanceReturnRun run ++ match rest with
    | [] => []
    | binding :: tail => binding :: balanceReturnSequence tail

private partial def balanceReturnBlocks (e : SExpr) : SExpr :=
  mapE (fun
    | .block p ss => some (.block p (balanceReturnSequence (ss.map balanceReturnBlocks)))
    | _ => none) e

partial def needsReturnBoundary : SExpr → Bool
  | .app _ (.ident _ "$returnBoundary") _ false => false
  | e@(.forE ..) | e@(.loop ..) => hasReturn e
  | .decl _ _ _ _ body => hasReturn body
  | .block _ values => values.any needsReturnBoundary
  | .ite _ _ yes no => needsReturnBoundary yes || no.any needsReturnBoundary
  | .caseE _ _ arms => arms.any fun (_, body) => needsReturnBoundary body
  | _ => false

/-- Retain the existing plain-return shape, and preserve scope boundaries
    when a returning function also has cleanup. -/
def elimReturns (fresh : Nat → String) (n : Nat) (multi : SExpr → Bool := fun _ => false)
    (ret : Option STy := none) (ss : List SExpr) (tailBlocks : Bool := false)
    (many : SExpr → Bool := hasLiftable) : Option (List SExpr × Nat) :=
  let nested := ss.any needsReturnBoundary
  if nested || (ss.map countRetIfs).foldl (· + ·) 0 > 16 then
    match ret with
    | some ty =>
      let balanced := balanceReturnSequence ((tailReturns ss).map balanceReturnBlocks)
      elimLinearReturns fresh ty false n ((ss.head?.map (·.pos)).getD default) balanced [] [] many (if nested then multi else returnChoices) tailBlocks
    | none => none
  else if ss.any (anyE isDefer) then
    elimScopedReturns fresh multi ret n ((ss.head?.map (·.pos)).getD default) (tailReturns ss) [] []
  else elimPlainReturns fresh n multi ret tailBlocks ss

/-- A function's name as written: a method's function `C$M` as `C.M`, and
    `F$all` as `F` (#283). -/
def shownFnName (n : String) : String :=
  let n := if n.endsWith "$all" then String.ofList (n.toList.take (n.length - 4)) else n
  -- (an overload's own name, #283, `F$mvK`, or an overloaded method's,
  -- `C$M$ovK`: its function's or method's)
  let base (sep n : String) : String := match n.splitOn sep with
    | [f, k] => if !f.isEmpty && k.all Char.isDigit && !k.isEmpty then f else n
    | _ => n
  let n := base "$ov" (base "$mv" (base "$copy" n))
  if n.startsWith "$" then n else (n.replace "::" ".").replace "$" "."

/-- The calls of `g` in `e` (its consumer's code, #246) as `$rec(args)`. -/
def markRec (g : String) : SExpr → SExpr :=
  mapE fun
    | .app p (.ident _ h) as _ => if h == g then some (.app p (.ident p "$rec") as false) else none
    | _ => none

/-- (#283) A call of another function of `g`'s group, `grp`, marked
    `$recTo(H, args)`; one of `g` itself `$rec(args)`. -/
def markRecG (g : String) (grp : List String) : SExpr → SExpr :=
  mapE fun
    | .app p (.ident q h) as _ =>
      if h == g then some (.app p (.ident p "$rec") as false)
      else if grp.contains h then some (.app p (.ident p "$recTo") (.ident q h :: as) false)
      else none
    | _ => none

/-- (#283) Whether `n` is a copy of a function that `instanceCopies` made,
    `F$copyK`. -/
def isInstanceCopy (n : String) : Bool :=
  match n.splitOn "$copy" with
  | [f, k] => !f.isEmpty && !k.isEmpty && k.all Char.isDigit
  | _ => false

/-- (#283) The holes of a copy's frames (`instanceCopies`) renamed for it,
    `$frame…@F$copyK`: one machine may take the copy and the function it is a
    copy of, whose frames are told apart by their holes (`loopFlatWith`'s
    `$sameFrame`, `firstBody`). -/
def copyHoles (h : String) (e : SExpr) : SExpr :=
  let holes := (namesUsed e).filter (·.startsWith "$frame")
  renameE (holes.eraseDups.map fun n => (n, s!"{n}@{h}")) e

/-- Replace each call of a function of `mv` by `$inline(F, template, args…)`,
    each with its own call site (`n`, the sites so far); a call of one of
    `loops` by `$loop(F, …)` (#246). -/
partial def inlineCalls (mv : List (String × MFn)) (e : SExpr) (recs : List String := [])
    (loops : List String := []) (clash : List (String × List String) := [])
    (inDflt : List (String × String) := []) (groups : List (String × List String) := [])
    (fieldOrder : String → FieldOrder := fun _ => {}) (memberFns : List (String × MFn) := [])
    (sitePrefix : String := "") :
    StateT Nat (Except String) SExpr := do
  -- (`inDflt`: the defaults being inlined, function and parameter, #283;
  -- `memberFns`: the functions a group's machine takes that are inlined
  -- elsewhere, with their returns taken out as the group's are, #283)
  let go := fun x => inlineCalls mv x recs loops clash inDflt groups fieldOrder memberFns sitePrefix
  match e with
  | .app p (.ident _ "$dispatch") (.ident q g :: .block tp tmpl :: as) false =>
    -- (an overridden method's dispatch, #283: an inlined call whose
    -- template binds the receiver and the arguments, then picks the
    -- implementation, its names tagged for this site)
    let site ← modifyGet fun n => (n, n + 1)
    if site ≥ 2000 then
      throw s!"{p.show}: more than 2000 calls of functions with several values to inline: nested calls multiply them (#235)"
    let ren := (localsOf (.block tp tmpl)).map fun n => (n, s!"${g.replace "::" "_"}_{n}_{sitePrefix}{site}")
    -- (a generic family's type parameters, named for the call, for this
    -- site too, #283: a body inlined twice has its dispatch twice)
    let tpNames : List String := tmpl.flatMap fun
      | .app _ (.ident _ "$tparams") (_ :: tps) false => tps.filterMap fun
          marker => (TParam.ofMarker marker).toOption.map (·.name)
      | _ => []
    let ρt := tpNames.map fun n => (n, s!"{n}s{sitePrefix}{site}")
    let renTps : SExpr → SExpr
      | .app q (.ident q2 "$tparams") (fnm :: tps) false =>
        .app q (.ident q2 "$tparams") (fnm :: tps.map fun
          marker => match TParam.ofMarker marker with
            | .ok tp => (tp.rename ρt).marker marker.pos
            | .error _ => marker) false
      | x => renameTypes ρt x
    let tmpl := if ρt.isEmpty then tmpl else tmpl.map renTps
    let tmpl' ← (tmpl.map (renameE ren)).mapM go
    return .app p (.ident p "$inline") (.ident q g :: .block tp tmpl' :: (← as.mapM go)) false
  | .app p (.ident q g) as br =>
    match mv.lookup g with
    | some f =>
      -- (as at a call: several arguments to a single array parameter, and
      -- one tuple argument to several parameters, #134, #140)
      -- (named parameters, #283: none of that, as at such a call)
      let hasNamed := f.params.any (·.named)
      let posPs := f.params.filter (!·.named)
      -- Literal tuple fields participate in generic method inference one
      -- at a time, so an earlier value can type a later empty container.
      let namedArg := fun | SExpr.decl _ n _ _ _ => n.startsWith "?" | _ => false
      let selfP := f.params.head?.any (·.name == "$Self")
      let classTps := match f.params.head?.map (·.ty) with
        | some (.app _ ts) => ts.length
        | _ => 0
      let as := if selfP && f.tparams.length > classTps && posPs.length >= 3 then
          match as.filter (!namedArg ·) with
          | [receiver, .tuple _ fields] =>
            if fields.length == posPs.length - 1 then receiver :: fields ++ as.filter namedArg else as
          | _ => as
        else as
      -- Pack a call's user arguments before the inliner's arity gate, just
      -- as the checked binder does. The receiver stays outside the tuple.
      let off := if selfP then 1 else 0
      let userArgs := (as.filter (!namedArg ·)).drop off
      let as := match posPs.drop off with
        | [sp] =>
          let value : Option SExpr := match sp.ty with
            | .tup [_] => match userArgs with
              | [a] => some (.app p (.ident p "$callSingleton") [a] false)
              | _ => some (SExpr.tuple p userArgs)
            | .tup _ => if userArgs.length != 1 then some (SExpr.tuple p userArgs) else none
            | .arr _ => if userArgs.length > 1 then some (SExpr.arrayLit p userArgs) else none
            | .name n =>
              if (n == "void" && userArgs.isEmpty) || (f.tparams.any (·.name == n) && userArgs.length != 1) then
                some (SExpr.tuple p userArgs)
              else none
            | _ => none
          match value with
          | some a => (as.filter (!namedArg ·)).take off ++ [a] ++ as.filter namedArg
          | none => as
        | _ => as
      let posAs := as.filter fun | .decl _ n _ _ _ => !n.startsWith "?" | _ => true
      let namedAs : List (Pos × String × SExpr) := as.filterMap fun
        | .decl ap n _ _ x => if n.startsWith "?" then some (ap, (n.drop 1).toString, x) else none
        | _ => none
      -- (a method's function, #283: its receiver first, then the arguments
      -- as a method's; no array form for a method, as at its call)
      let arrayParam := !hasNamed && !selfP && match f.params with | [sp] => (match sp.ty with | .arr _ => true | _ => false) | _ => false
      let tupleArg := !hasNamed && as.length == 1 + off && f.params.length ≥ 2 + off
      -- (one tuple for the positional parameters, followed by supplied
      -- named arguments and omitted defaults)
      let tupleNamed := hasNamed && posAs.length == 1 + off && posPs.length ≥ 2 + off
      if hasNamed then
        if posAs.length != posPs.length && !tupleNamed then
          throw s!"{p.show}: {shownFnName g} takes {posPs.length - off} positional argument(s), found {posAs.length - off}"
        for ((ap, n, _), i) in namedAs.zipIdx do
          if !(f.params.any fun sp => sp.named && sp.name == n) then throw s!"{ap.show}: {shownFnName g} has no parameter ?{n}"
          if (namedAs.take i).any (·.2.1 == n) then throw s!"{ap.show}: ?{n} is given twice"
        for sp in f.params do
          if sp.named && sp.default.isNone && !namedAs.any (·.2.1 == sp.name) then
            throw s!"{p.show}: {shownFnName g} needs the argument ?{sp.name}, which has no default"
      else
        if as.length != f.params.length && !arrayParam && !tupleArg then
          throw s!"{p.show}: {shownFnName g} takes {f.params.length - off} argument(s), found {as.length - off}"
        if !namedAs.isEmpty then
          throw s!"{p.show}: {shownFnName g} has no named parameters"
      if br != f.fx.contains "decides" then
        throw (if br then s!"{p.show}: {shownFnName g} is not <decides>: call it with {shownFnName g}(…)"
          else s!"{p.show}: {shownFnName g} is <decides>: call it with {shownFnName g}[…]")
      -- (with named parameters, the positional arguments' then the named
      -- ones' values, as evaluated)
      let as' ← if hasNamed then pure [] else as.mapM go
      let posVals ← if hasNamed then posAs.mapM go else pure []
      let namedVals ← if hasNamed then namedAs.mapM (fun (_, _, x) => go x) else pure []
      -- (a recursive one: the array of its values, computed at the call)
      if recs.contains g && !loops.contains g && !hasNamed then
        return .app p (.ident p "$each") [.app p (.ident q s!"{g}$all") as' false] false
      let site ← modifyGet fun n => (n, n + 1)
      if site ≥ 2000 then
        throw s!"{p.show}: more than 2000 calls of functions with several values to inline: nested calls multiply them (#235)"
      let tag (n : String) : String := s!"${g.replace "::" "_"}_{n}_{sitePrefix}{site}"
      let ren := (f.params.map (·.name) ++ localsOf f.body).eraseDups.map fun n => (n, tag n)
      -- (a generic one's type parameters renamed for this site, #235: its
      -- parameters are bound together, the type arguments inferred from
      -- the arguments as at a call, `$params`, which then names them for
      -- the written types after)
      let ρ : List (String × String) := f.tparams.map fun tp => (tp.name, s!"$tp{sitePrefix}{site}_{tp.name}")
      let tyOf (t : STy) : Option STy := some (styRename ρ t)
      let tmark : List SExpr := (if ρ.isEmpty then [] else
        [.app q (.ident q "$tparams") (.ident q g :: (ρ.zip f.tparams).map fun ((_, n), tp) =>
          ({ tp.rename ρ with name := n } : TParam).marker q) false]) ++
        -- (the names its body uses from outside, checked not in scope here)
        (match clash.lookup g with
         | some us => [.app q (.ident q "$freeNames") (.ident q g :: us.map (SExpr.ident q ·)) false]
         | none => [])
      -- (with named parameters: the positional ones, then the named ones
      -- given, as written, then the defaults of those omitted, in order,
      -- each in its own context, `$paramDefault`, as at a call)
      let markValue (sp : SParam) (value : SExpr) :=
        if sp.typeValue then SExpr.app q (.ident q "$typeValue") [value] false else value
      let pdOf (sp : SParam) : SExpr := .decl q (tag sp.name) (tyOf sp.ty) false (markValue sp (.ident q "$arg"))
      let dflts ← if !hasNamed then pure [] else
        f.params.zipIdx.filterMapM fun (sp, k) => do
          match sp.default with
          | some d =>
            if !sp.named || namedAs.any (·.2.1 == sp.name) then return none
            -- (one that calls `g` again omitting it: as at a call)
            if inDflt.contains (g, sp.name) then
              throw s!"{p.show}: the default of ?{sp.name} of {shownFnName g} uses itself (a call of {shownFnName g} that omits ?{sp.name})"
            let d' ← inlineCalls mv (renameTypes ρ d) recs loops clash ((g, sp.name) :: inDflt) groups fieldOrder memberFns sitePrefix
            let earlier := (f.params.take k).map fun e => SExpr.tuple q [.ident q e.name, .ident q (tag e.name)]
            return some (.decl q (tag sp.name) (tyOf sp.ty) false
              (markValue sp (.app q (.ident q "$paramDefault") [.ident q g, .ident q sp.name, .block q earlier, d'] false)))
          | none => return none
      -- (a generic one's: together, after its `$params`, `$defaults`, so a
      -- default can give a type parameter nothing else determined its type
      -- argument, as at a call, #392's review)
      let dflts : List SExpr := if ρ.isEmpty || !hasNamed then dflts else
        [.app q (.ident q "$defaults") (.block q dflts :: .ident q g :: (ρ.zip f.tparams).map fun ((_, n), tp) =>
          ({ tp.rename ρ with name := n } : TParam).marker q) false]
      let (pds, unpack, as'') : List SExpr × List SExpr × List SExpr :=
        if tupleNamed then
          let t := tag "$tuple"
          let tps := posPs.drop off
          ((posPs.take off).map pdOf ++ [.decl q t (tyOf (.tup (tps.map (·.ty)))) false (.ident q "$arg")] ++
              namedAs.filterMap (fun (_, n, _) => (f.params.find? (·.name == n)).map pdOf),
            (tps.zipIdx.map fun (sp, i) =>
              SExpr.decl q (tag sp.name) (tyOf sp.ty) false (markValue sp (.app q (.ident q t) [.int q (i : Int)] false))) ++ dflts,
            posVals ++ namedVals)
        else if hasNamed then
          (posPs.map pdOf ++ namedAs.filterMap (fun (_, n, _) => (f.params.find? (·.name == n)).map pdOf), dflts,
            posVals ++ namedVals)
        else if as.length == f.params.length then
          (f.params.map pdOf, [], as')
        else if arrayParam then
          (f.params.map pdOf, [],
            [.arrayLit p as'])
        else
          -- (the tuple bound once, its elements into the parameters; a
          -- method's receiver first)
          let t := tag "$tuple"
          let tps := f.params.drop off
          ((f.params.take off).map pdOf ++ [.decl q t (tyOf (.tup (tps.map (·.ty)))) false (.ident q "$arg")],
            (tps.zipIdx.map fun (sp, i) =>
              SExpr.decl q (tag sp.name) (tyOf sp.ty) false (markValue sp (.app q (.ident q t) [.int q (i : Int)] false))), as')
      -- Eager recursive calls still bind named arguments/defaults exactly
      -- as an inlined call. The array helper receives canonical parameters.
      if recs.contains g && !loops.contains g then
        let values := .app p (.ident p "$each")
          [.app p (.ident q s!"{g}$all") (f.params.map fun sp => .ident q (tag sp.name)) false] false
        return .app p (.ident p "$inline") (.ident q g ::
          .block q (tmark ++ pds ++ unpack ++ [.decl q (tag "$r") (tyOf f.ret) false values]) :: as'') false
      -- (one taken lazily, #246: its parameters, its clauses and its last
      -- expression, its own calls marked, for its consumer to run)
      if loops.contains g then
        let grp := (groups.lookup g).getD [g]
        let some (cls, tail) := loopShape? g (mv.map (·.1)) (renameTypes ρ (renameE ren f.body)) grp (frames := true)
            (f.params.map (tag ·.name)) fieldOrder
          | throw s!"{p.show}: internal: the shape of {g} (#246)"
        let ps := f.params.map fun sp => SExpr.ident q (tag sp.name)
        -- (#283) a function of a strongly connected group: the others'
        -- parameters, clauses and last expressions too, each's names
        -- tagged for this site, in `$group(tail, $member(H, params,
        -- clauses, r := tail)…)`
        let tail' ← if grp.length ≤ 1 then pure (markRec g tail) else do
          let mut members : List SExpr := []
          for h in grp.filter (· != g) do
            let some fh := (memberFns.lookup h).orElse fun _ => mv.lookup h
              | throw s!"{p.show}: internal: the group of {g} (#283)"
            let tagH (n : String) : String := s!"${h.replace "::" "_"}_{n}_{sitePrefix}{site}"
            let renH := (fh.params.map (·.name) ++ localsOf fh.body).eraseDups.map fun n => (n, tagH n)
            let ρH := fh.tparams.map fun tp => (tp.name, memberTypeName h tp.name)
            let some (clsH, tailH) := loopShape? h (mv.map (·.1)) (renameTypes ρH (renameE renH fh.body)) grp (frames := true)
              (fh.params.map (tagH ·.name)) fieldOrder
              | throw s!"{p.show}: internal: the shape of {h} (#283)"
            let (clsH, tailH) := if isInstanceCopy h then (clsH.map (copyHoles h), copyHoles h tailH) else (clsH, tailH)
            members := members ++ [.app q (.ident q "$member") [.ident q h,
              .block q (fh.params.map fun sp => SExpr.ident q (tagH sp.name)), .block q clsH,
              .decl q (tagH "$r") (some (styRename ρH fh.ret)) false (markRecG h grp tailH)] false]
          pure (.app q (.ident q "$group") (markRecG g grp tail :: members) false)
        -- (the names the others' bodies use from outside too, checked not
        -- in scope here, as for its own, #371's review)
        let memberFrees : List SExpr := (grp.filter (· != g)).filterMap fun h =>
          (clash.lookup h).map fun us => .app q (.ident q "$freeNames") (.ident q h :: us.map (SExpr.ident q ·)) false
        return .app p (.ident p "$loop") (.ident q g :: .block q (tmark ++ memberFrees ++ pds ++ unpack) :: .block q ps ::
          .block q cls :: .decl q (tag "$r") (tyOf f.ret) false tail' :: as'') false
      let body ← go (renameTypes ρ (renameE ren f.body))
      -- Returning bodies keep registrations in their lexical scopes until
      -- return normalization. Other bodies keep the existing value cleanup.
      let ss := stmtsOf body
      let hasRet := hasReturn body
      let ds := if hasRet then [] else deferBodies ss
      -- (one ending in a `defer:`, a `void` one: they are its value, a block
      -- of them, as a block ending in one has)
      let lastD := ss.getLast?.any isDefer
      let body := if ds.isEmpty then body else
        .block q (ss.filter (!isDefer ·) ++ (if lastD then [.block q ds] else []))
      let ds := if lastD then [] else ds
      -- (its `return`s as guarded alternatives, #283)
      let ss := stmtsOf body
      let ss ← if hasRet then do
          let some (normalized, _) := elimReturns (fun i => tag s!"$k{i}") 0
            (fun b => (stmtsOf b).any liftsHere || hasChoice (stmtsOf b)) (tyOf f.ret) ss
            | throw s!"{q.show}: {shownFnName g} has a return in an unsupported expression: a loop or binding initializer with a return must be single-valued and cannot start concurrent work (#686, #687)"
          pure normalized
        else pure ss
      let r := tag "$r"
      let (init, last) := (ss.dropLast, ss.getLast?)
      let (init, res) : List SExpr × SExpr := match last with
        | some (.decl q2 x t v rhs) => (init ++ [.decl q2 x t v rhs], .ident q2 x)
        | some l => (init, l)
        | none => (init, .tuple q [])
      let fin : List SExpr := if ds.isEmpty then [.decl q r (tyOf f.ret) false res] else
        [.decl q (tag "$r0") (tyOf f.ret) false res, .block q (ds ++ [.int q 0]),
          .decl q r (tyOf f.ret) false (.ident q (tag "$r0"))]
      let tmpl := SExpr.block q (tmark ++ pds ++ unpack ++ init ++ fin)
      return .app p (.ident p "$inline") (.ident q g :: tmpl :: as'') false
    | none => return .app p (← go (.ident q g)) (← as.mapM go) br
  | e => descendM go e

/-- A generator of `x` over the array `src` (#235); at a written type `ty`,
    one of a name of its own, `$e…` (with `site` in it, `madeName`), then
    `x` bound to it at `ty`. -/
def genOver (site : String) (q : Pos) (x : String) (ty : Option STy) (src : SExpr) : List SExpr :=
  match ty with
  | none => [.gen q x none src]
  | some t =>
    let e := madeName "e" site q ++ "$" ++ x
    [.gen q e none src, .decl q x (some t) false (.ident q e)]

mutual
/-- The array of an expression's values, for a `$all` body (#235): a choice
    concatenates its alternatives' arrays, an `if` with choices in its
    branches picks a branch's, and any other expression is the array of the
    values of its own clauses (`gensOf`): of its value, empty when it fails,
    and through the choices and calls of functions with several values
    (marked `$each`) inside it. So an alternative that fails, or whose
    argument does, gives no values, and the others still do. At the written
    type `ty`, when there is one. -/
partial def arrOfE (ty : Option STy := none) (fieldOrder : String → FieldOrder := fun _ => {}) : SExpr → SExpr
  | .app p (.ident _ "$methodMiss") [] false =>
    match ty with
    | none => .arrayLit p []
    | some t =>
      let empty := s!"$noMethodValues{p.line}_{p.col}"
      .block p [.decl p empty (some (.arr t)) false (.arrayLit p []), .ident p empty]
  | .app p (.ident _ "$choice") as false =>
    match as with
    | [a] => arrOfE ty fieldOrder a
    | _ => .app p (.ident p "Concatenate") (as.map (arrOfE ty fieldOrder)) false
  | .ite p cs t (some e) => .ite p cs (arrOfE ty fieldOrder t) (some (arrOfE ty fieldOrder e))
  | a =>
    let p := a.pos
    let site := s!"a{p.line}_{p.col}"
    let v := s!"$a{p.line}_{p.col}"
    .forE p (gensOf site [.decl p v ty false a] fieldOrder) (.ident p v)

/-- Clauses for a `for` that goes through all their values (#235): each
    choice a generator over the array of its alternatives' values, each
    call of a recursive function with several values one over its array.
    Names made include `site`, so that nested ones differ. -/
partial def gensOf (site : String) (cs : List SExpr)
    (fieldOrder : String → FieldOrder := fun _ => {}) : List SExpr :=
  (prepare cs (site := site) (fieldOrder := fieldOrder) (guardBranches := false)).flatMap fun c => match binding? c with
    | some { pos := q, name := x, ty := ty, alts := as, branchy := none, each := none, .. } =>
      genOver site q x ty (arrOfE ty fieldOrder (.app q (.ident q "$choice") as false))
    | some { pos := q, name := x, ty := ty, branchy := some i, .. } => genOver site q x ty (arrOfE ty fieldOrder i)
    | some { pos := q, name := x, ty := ty, each := some a, .. } => genOver site q x ty a
    | _ => [c]
end

/-- Each call of a function of `mvs` marked as the array of its values,
    `$each(F$all(args))`, also in the arguments of others. -/
partial def markAll (mvs : List String) : SExpr → SExpr :=
  mapE fun
    | .app p (.ident q g) as _ =>
      if mvs.contains g then
        some (.app p (.ident p "$each") [.app p (.ident q s!"{g}$all") (as.map (markAll mvs)) false] false)
      else none
    | _ => none

/-- The body of `F$all`, the array of `F`'s values in order (#235): one
    `for` over its clauses (`gensOf`), whose value is `F`'s, at its result
    type `ret`. (`F` is effect-free, so evaluating the clauses in this order
    changes nothing.) -/
def allBody (mvs : List String) (ret : STy) (b : SExpr) : SExpr :=
  -- (an overridden method's dispatch, #283: a choice of its alternatives,
  -- the receiver and the arguments bound before; exact, as effect-free)
  let ss := stmtsOf (markAll mvs (exclToChoice (dispatchBlocks b) (deep := true)))
  let p := b.pos
  let (cs, v) : List SExpr × SExpr := match ss.getLast? with
    | some (.decl q x _ _ _) => (ss, .ident q x)
    | some l => (ss.dropLast ++ [.decl l.pos "$val" (some ret) false l], .ident l.pos "$val")
    | none => ([], .tuple p [])
  -- Field layouts and contextual construction instances belong to the
  -- elaborator. Keep the clauses intact until it can supply them to gensOf.
  .app p (.ident p "$allValues") [.block p cs, v] false

/-- A name of `mv` used other than as a call's head: as a function value. -/
partial def valueUse? (mv : List String) : SExpr → Option (Pos × String)
  -- (a dispatch names the family's function for its messages, #283)
  | .app _ (.ident _ "$dispatch") (_ :: as) _ => as.findSome? (valueUse? mv)
  | .app _ (.ident _ _) as _ => as.findSome? (valueUse? mv)
  | .ident p n => if mv.contains n then some (p, n) else none
  | .structDef _ _ _ fs => (fs.filterMap (·.default)).findSome? (valueUse? mv)
  | e => e.children.findSome? (valueUse? mv)

/-- Source storage retained by a generated resume method. The method's
    locals are initialized from its environment, then borrow these origins. -/
structure ResumeStorage where
  frame : String
  name : String
  args : List STy
  deriving Inhabited

/-- Lexical restrictions and active default dependencies survive moving
    source expressions into a generated continuation. -/
structure SourceContext where
  inCtor : Bool := false
  inParamDefault : Bool := false
  inBlock : Bool := false
  inDefer : Bool := false
  inDefaultCheck : Bool := false
  inRepeat : Bool := false
  inChoice : Bool := false
  inArm : Bool := false
  inBranch : Bool := false
  defaults : List (String × String) := []
  /-- (#515, `--default-no-rollback` only) The source body excludes
      `no_rollback` (`Ctx.rollbackOnly`), or is a plain `<decides>` one's
      (`Ctx.bodyFailure`). -/
  rollbackOnly : Bool := false
  bodyFailure : Bool := false
  deriving Inhabited, BEq, Repr

/-- Metadata for a typed continuation environment's method. -/
structure ForResume where
  name : String
  /-- Source rollback ownership, independent of a resume's physical frame. -/
  rollback : Bool := false
  /-- A compiler-only consumer keeps structured children in its source caller. -/
  borrowTasks : Bool := false
  storage : List (String × ResumeStorage) := []
  /-- Typed borrowed owners forwarded without reading an aliased field. -/
  forwarded : List ResumeStorage := []
  inlineScopes : List String := []
  liftTag : String := ""
  inRepeat : Bool := true
  inChoice : Bool := false
  sourceContext : SourceContext := {}
  deriving Inhabited

/-- One filter's typed handoff to work that executes after it commits. -/
structure ForStagePlan where
  key : String
  /-- A refinement prefix prepares a different world from the committing
      body. Retain the body's original lexical and rollback ownership. -/
  resumeContext : Option SourceContext := none
  /-- Only a real source collector body carries this capability. Protocol
      source/filter stages keep their existing private failure context. -/
  resumeCanFail : Option Bool := none
  resumeRollback : Bool := false
  /-- Immediate refinement environments receive current caller copy-ins
      when resumed, after prefix cleanup has finished. -/
  resumeInputs : Bool := false
  /-- A source-array stage keeps ordinary for search lowering. -/
  resumeOriginalFor : Bool := false
  pos : Pos
  base : String
  method : String
  tparams : List TParam
  value : STy
  copies : List (String × STy)
  borrowed : List String
  specs : List String
  outcome : Bool := false
  /-- Source operations requiring a suspending context, excluding task starts. -/
  sourceSuspends : Bool := false
  deriving Inhabited

/-- (#246) A lazily taken call, where the first success is taken, whose
    clauses, conditions or calls of itself have effects: compiled as a
    function of its own, recursive, so that each alternative and each call
    of itself is a failure context of its own, undone with its values as
    the Verse Calculus does. It takes the function's parameters and the
    consumer's names that the clauses after the call use (`args`, at the
    consumer), and gives, at the first success of those clauses, the names
    they bind and the final values of the `var`s they set (`binds`, then
    `sets`, then `true`). -/
structure FirstLift where
  sourceContext : SourceContext := {}
  /-- (#515, `--signal-no-rollback`) A `for`'s continuation made inside a
      failure context where the code cannot fail (`Ctx.inRollback`): its
      body runs inside that context too. -/
  rollback : Bool := false
  /-- A stage request supplies classes rather than a callable helper. -/
  stageOnly : Bool := false
  resumes : List ForResume := []
  stagePlan : Option ForStagePlan := none
  inlineScopes : List String := []
  /-- A class-copy context remains valid after moving its code. -/
  liftTag : String := ""
  key : String
  pos : Pos
  name : String
  params : List SParam
  tparams : List TParam := []
  specs : List String
  ret : STy
  /-- Normalize a polymorphic result after inferring its input instance. -/
  joinedRet : Option STy := none
  body : SExpr
  binds : List String
  sets : List String
  args : List SExpr
  /-- Bind operation dictionaries at each alternative's precise instance. -/
  casePrelude : List (List SExpr) := []
  /-- The names of `binds` that are `var`s, bound so again. -/
  varBinds : List String := []
  /-- (#283) For a call of a function of a strongly connected group: the
      other functions of the group, one function of its own each, which the
      function and they call for one another. -/
  extraFns : List STop := []
  /-- New raw producer adapters must pass ordinary method-family inlining.
      Existing prepared continuations remain in their later source phase. -/
  sourceFns : List STop := []
  deriving Inhabited

/-- (#246) A value of a lazily taken call, in its function of its own: at the
    function's result type `ret`, then bound to the binding `b`, then the
    consumer's clauses after the call (`rest`, lifted already, `$firstP`,
    which lifting again would bind twice), then the tuple `tup` of what they
    bind. -/
def firstValue (b : String) (bty ret : Option STy) (rest : List SExpr) (tup : SExpr) (a : SExpr) : SExpr :=
  let v := match ret with
    | some t => SExpr.app a.pos (.ident a.pos "$first") [.block a.pos [.decl a.pos s!"{b}$v" (some t) false a,
        .ident a.pos s!"{b}$v"]] false
    | none => a
  .app a.pos (.ident a.pos "$firstP") [.block a.pos ([.decl a.pos b bty false v] ++ rest ++ [tup])] false

/-- (#283) The body of a `FirstLift`'s function that takes each value `$V`
    of a lazily taken call with return frames: the value given to the
    continuation `$K`'s frames (`$frameApply`), then as `firstValue`. -/
def firstReturnBody (p : Pos) (b : String) (bty : Option STy) (rest : List SExpr) (binds : List String)
    (sets : List (String × STy)) (ret : Option STy)
    (frames : List (String × List String × SExpr)) (memberFn : Nat → Option String := fun _ => none)
    (caps : List SExpr := []) (frameTys : List (Option STy × Option STy) := []) : SExpr :=
  let tup : SExpr := .tuple p (binds.map (SExpr.ident p ·) ++ sets.map (fun (m, _) => SExpr.ident p m) ++
    [.ident p "true"])
  let copies := sets.map fun (m, t) => SExpr.decl p m (some t) true (.ident p s!"{m}$in")
  let liveIds (lives : List String) : List SExpr := lives.map (SExpr.ident p ·)
  if (List.range frames.length).all (memberFn · |>.isNone) && frameTys.all (fun (i, o) => i.isNone && o.isNone) then
    let v := SExpr.app p (.ident p "$frameApply") (.ident p "$K" :: .ident p "$V" :: frames.map fun (h, lives, code) =>
      .app p (.ident p "$frame") [.ident p h, .block p (liveIds lives), code] false) false
    .block p (copies ++ [firstValue b bty ret rest tup v])
  else
  -- (#283) with continuation members: a member's frame calls its function
  -- with the value, its lives and the rest of the continuation, whose packet
  -- is this one's; when no frame is left, the value as `firstValue`, `$Vfin`
  -- at the result type; a frame's hole's and code's types when other ones
  let tys (j : Nat) : List SExpr := match frameTys[j]? with
    | some (i, o) => if i.isNone && o.isNone then [] else
      [.block p ((i.toList.map fun t => SExpr.decl p "$in" (some t) false (.tuple p [])) ++
        o.toList.map fun t => SExpr.decl p "$out" (some t) false (.tuple p []))]
    | none => []
  let entry (j : Nat) (h : String) (lives : List String) (code : SExpr) : SExpr := match memberFn j with
    | some fn => .app p (.ident p "$frameCall") ([.ident p h, .block p (liveIds lives),
        .app p (.ident p fn) (.ident p h :: liveIds lives ++ [.ident p "$Krest"] ++ caps) true] ++ tys j) false
    | none => .app p (.ident p "$frame") ([.ident p h, .block p (liveIds lives), code] ++ tys j) false
  -- (with a frame of another type, the final value in a name of its own)
  let fin : List SExpr := if frameTys.all (fun (i, o) => i.isNone && o.isNone) then
      [firstValue b bty ret rest tup (.ident p "$V")]
    else [.block p [.decl p "$Vfin" ret false (.tuple p [])], firstValue b bty ret rest tup (.ident p "$Vfin")]
  .block p (copies ++ [.app p (.ident p "$frameReturn") (.ident p "$K" :: .ident p "$V" ::
    fin ++ frames.zipIdx.map fun ((h, lives, code), j) => entry j h lives code) false])

/-- The body of a `FirstLift` (#246): the function's clauses, then the first
    success of its last expression, each value followed by the consumer's
    clauses after the call (`rest`, the value bound to `b` first) and the
    tuple of what they bind, each call of itself a call of `helper` with the
    captured names after its arguments. The `var`s the clauses set are
    copied first from parameters named `m$in`. With return frames (#283,
    `frames`: each one's hole, lives and code), the continuation `$K` comes
    after the arguments: a call with code after it pushes its frame on it,
    and a value is given to it, then to the clauses after the call, by the
    function `retFn` (`firstReturnBody`), so that the frames' code and those
    clauses are not copied into each value. -/
partial def firstBody (helper : String) (p : Pos) (b : String) (bty : Option STy) (cls : List SExpr) (tail : SExpr)
    (rest : List SExpr) (binds : List String) (sets : List (String × STy)) (caps : List SExpr)
    (ret : Option STy := none) (helperOf : String → String := fun _ => helper)
    (recArgs : Option String → Pos → List SExpr → List SExpr × List SExpr := fun _ _ as => ([], as))
    (frames : List (String × List String × SExpr) := [])
    (retFn : String := "") (frameTys : List (Option STy × Option STy) := [])
    (retOf : Option STy → String := fun _ => retFn) (ownTy : Option STy := none) : SExpr :=
  let tup : SExpr := .tuple p (binds.map (SExpr.ident p ·) ++ sets.map (fun (m, _) => SExpr.ident p m) ++
    [.ident p "true"])
  let recur (target : Option String) (h : String) (q : Pos) (as : List SExpr) (k : List SExpr) : SExpr :=
    let (pre, args) := recArgs target q as
    let call := SExpr.app q (.ident q h) (args ++ k ++ caps) true
    if pre.isEmpty then call else .block q (pre ++ [call])
  let call (k : List SExpr) : SExpr → Option SExpr
    | .app q (.ident _ "$rec") as false => some (recur none helper q as k)
    -- (a call of another function of the group, #283: its own function)
    | .app q (.ident _ "$recTo") (.ident _ h :: as) false => some (recur (some h) (helperOf h) q as k)
    | _ => none
  -- (the continuation `$K` with the frames `fs` pushed on it, innermost
  -- first: each its index, its lives and where)
  let pushed (fs : List (Nat × List SExpr × Pos)) (q0 : Pos) : SExpr :=
    fs.foldr (fun (j, lives, q) acc => .app q (.ident q "$framePush") (.int q (j : Int) :: acc :: lives) false)
      (.ident ((fs.getLast?.map (·.2.2)).getD q0) "$K")
  -- (a value, given to the continuation's frames, #283: by the function for
  -- its type, the first frame's hole's, or else this code's own)
  let valueTo (fs : List (Nat × List SExpr × Pos)) (a : SExpr) : SExpr :=
    let t := match fs.head? with
      | some (j, _, _) => (frameTys[j]?).bind (·.1)
      | none => ownTy
    .app a.pos (.ident a.pos (retOf t)) ([a, pushed fs a.pos] ++ caps) true
  -- (an alternative whose values go to the frames `fs`, then `$K`)
  let rec altK (fs : List (Nat × List SExpr × Pos)) (a : SExpr) : SExpr :=
    match a with
    | .app q (.ident _ "$then") (c :: .ident _ h :: _ :: pre) false =>
      -- (#283) a choice point with code after it: its frame on the
      -- continuation, after its prefix, if any; a choice's on each of its
      -- alternatives' (`Choice.flatCount`)
      let j := (frames.findIdx? (·.1 == h)).getD 0
      let lives := (((frames[j]?).map (·.2.1)).getD []).map (SExpr.ident q ·)
      let fs' := (j, lives, q) :: fs
      match alts? c, c with
      | some cs, _ => mk q (cs.map (altK fs'))
      -- (a leaf of an `if` that is a point, with that frame after its own)
      | none, .app _ (.ident _ "$then") _ false => altK fs' c
      | none, _ =>
      match call [pushed fs' q] c, pre with
      | some e, [.block _ ss] => .block q (ss ++ [e])
      | some e, _ => e
      -- (a value entering a member, `enterOf`)
      | none, _ => valueTo fs' c
    | a =>
      match call (if frames.isEmpty then [] else [pushed fs a.pos]) a with
      | some c => c
      | none =>
      if frames.isEmpty then firstValue b bty ret rest tup a
      else valueTo fs a
  let alt := altK []
  let group (v : SExpr) : SExpr := match alts? v with
    | some as => mk v.pos (as.map alt)
    | none => alt v
  let tail' := mapLoopTail group tail
  let copies := sets.map fun (m, t) => SExpr.decl p m (some t) true (.ident p s!"{m}$in")
  .block p (copies ++ cls ++
    [.app p (.ident p "$first") [.block p [.decl p "$R" none false tail', .ident p "$R"]] false])

/-- The functions a call of which may have several values: (not `Main` or
    the entry expression, which nothing calls in a failure context, nor
    `<suspends>` functions, which cannot run in one). -/
def multiCandidates (tops : List STop) : List (String × MFn) :=
  tops.filterMap fun
    | .fn p n ps tps fx r b =>
      if n == "Main" || n == "$Do" || fx.contains "suspends" then none else some (n, ⟨p, ps, tps, fx, r, b⟩)
    | _ => none

/-- A returning iteration can expose choices through the rest of the
    producer. Header choices belong to the for search. -/
private partial def returningLoopChoice : SExpr → Bool
  | .forE _ _ body | .loop _ body =>
    hasReturn body && (hasChoice (stmtsOf body) || returningLoopChoice body)
  | .block _ statements => statements.any returningLoopChoice
  | .ite _ _ yes no => returningLoopChoice yes || no.any returningLoopChoice
  | .caseE _ _ arms => arms.any (fun (_, body) => returningLoopChoice body)
  | .decl _ _ _ _ value => returningLoopChoice value
  | _ => false

/-- Which of `fns` have several values, also through the calls of ones that
    have them, where the body itself does not take their values. -/
def multiValued (fns : List (String × MFn)) : List String := Id.run do
  let mut mv : List String := []
  let mut changed := true
  while changed do
    changed := false
    for (n, f) in fns do
      let b := markCalls mv f.body
      let ss := stmtsOf b
      -- (a choice in a `return`'s value too, #283)
      if !mv.contains n && (hasChoice ss || ss.any liftsHere || returningLoopChoice b ||
          anyE (fun | .ret _ (some e) => hasLiftable e | _ => false) b) then
        mv := mv ++ [n]; changed := true
  return mv

/-- The function that a `for` whose body has several values is a call of
    (`forProducts`), and the one that gives the values of one of its rows. -/
def forProductName : String := "$forProduct"
def forElemsName : String := "$forElems"

/-- Whether a `for` body has several values: a choice, or a call of one of
    the functions `mv`, that nothing in the body takes. One with a `return`
    is a returning loop (#686), which has its own lowering. -/
def forBodySeveral (mv : List String) (body : SExpr) : Bool :=
  !hasReturn body &&
    (let ss := stmtsOf (markCalls mv body)
     hasChoice ss || ss.any liftsHere)

/-- Each `for` in `e` whose body has several values as the call that has
    its values, innermost first, so that a `for` around one sees that call:

        for (cs) { b }   ⟶   $forProduct[for (cs) { for ($v := b) { $v } }, 0]

    The inner `for` collects the values of `b` for one iteration (a row);
    the call has one array for each way to pick a value from every row, the
    first row's choice varying slowest. This is the Verse Calculus's
    `for`, whose iterations' bodies are the elements of the array it
    builds, so that their choices are choices of the array. -/
partial def forProductsE (mv : List String) (e : SExpr) : SExpr :=
  match Id.run (descendM (m := Id) (fun c => pure (forProductsE mv c)) e) with
  | .forE p cs body =>
    if forBodySeveral mv body then
      let q := body.pos
      let v := madeName "fb" "" q
      .app p (.ident p forProductName)
        [.forE p cs (.forE q [.decl q v none false body] (.ident q v)), .int p 0] true
    else .forE p cs body
  | e => e

/-- The program with every `for` whose body has several values as the call
    that has them (`forProductsE`), and whether there is one, so that the
    two functions it calls (`helpers`, parsed) are to be added. A function
    whose `for` is rewritten has several values from then on, and a `for`
    whose body calls it is rewritten in turn: repeated until no function
    joins those that have several values. -/
def forProducts (helpers : List STop) (tops : List STop) : List STop × Bool := Id.run do
  let several (ts : List STop) : List String := multiValued (multiCandidates (ts ++ helpers))
  let uses (ts : List STop) : Bool := ts.any fun t =>
    t.code.any (anyE fun | .ident _ n => n == forProductName | _ => false)
  let mut tops := tops
  let mut mv := several tops
  for _ in [0:tops.length + 1] do
    tops := tops.map (STop.mapAll id (forProductsE mv))
    let mv' := several tops
    if mv' == mv then break
    mv := mv'
  return (tops, uses tops)

/-- (#283) The place of an overload among its function's, `K` of `F$ovK`,
    as the elaborator names it. -/
def overloadIndex? (o : String) : Option Nat :=
  match o.splitOn "$ov" with
  | [_, k] => k.toNat?
  | _ => none

/-- (#283) `e` with each call of an overloaded function of `ovs` whose
    overload an earlier elaboration found, by the call's place (`picks`: the
    overload as the elaborator names it, `F$ovK`, or none), a call of that
    overload's own function `F$mvK`, if `sel` says so. -/
partial def pickOverloads (ovs : List String) (picks : List (Pos × String)) (sel : String → Bool)
    (e : SExpr) : SExpr :=
  mapE (fun
    | .app p (.ident q f) as br => do
      guard (ovs.contains f)
      let k ← overloadIndex? (← picks.lookup p)
      let g := s!"{f}$mv{k}"
      guard (sel g)
      return .app p (.ident q g) (as.map (pickOverloads ovs picks sel)) br
    | _ => none) e

/-- (#283) `e` with each call of an overload's own function `F$mvK` of one
    of `ovs` a call of `F` again, as written, whose overload the elaborator
    picks (`pickOverloads` undone). -/
partial def unpickOverloads (ovs : List String) (e : SExpr) : SExpr :=
  mapE (fun
    | .app p (.ident q g) as br => match g.splitOn "$mv" with
      | [f, k] => if ovs.contains f && k.toNat?.isSome then
          some (.app p (.ident q f) (as.map (unpickOverloads ovs)) br) else none
      | _ => none
    | _ => none) e

/-- The calls `F(args)` in `e`, by their place (#283). -/
partial def callUses (e : SExpr) : List (Pos × String) :=
  (match e with | .app p (.ident _ f) _ _ => [(p, f)] | _ => []) ++ e.children.flatMap callUses

/-- The overloaded functions of `tops` (#74): the names defined more than
    once, as the elaborator takes them (not `Main`, not a module's member). -/
def overloadedFns (tops : List STop) : List String :=
  let ns := tops.filterMap fun | .fn _ n .. => some n | _ => none
  (ns.filter fun n => (ns.filter (· == n)).length > 1 && !n.contains '.' && n != "Main").eraseDups

/-- (#283) The overloads of function `f` of `tops`, each a function of its
    own, `f$mvK` (K its place among them, as the elaborator numbers them,
    `f$ovK`), with where it is defined. -/
def overloadsOf (tops : List STop) (f : String) : List (String × Pos × MFn) :=
  (tops.filterMap fun
    | .fn p n ps tps fx r b => if n == f then some (p, (⟨p, ps, tps, fx, r, b⟩ : MFn)) else none
    | _ => none).zipIdx.map fun ((p, m), k) => (s!"{f}$mv{k}", p, m)

/-- (#283) The functions of `tops` whose fixpoint says which have several
    values (`multiCandidates`, `multiValued`), each overload of an overloaded
    one a function of its own (`overloadsOf`), and each call whose overload
    an earlier elaboration picked (`picks`) one of that overload's function
    when `sel` says so; until then a call is as written, of one value. -/
def overloadCandidates (tops : List STop) (picks : List (Pos × String)) (sel : String → Bool) :
    List (String × MFn) :=
  let ovs := overloadedFns tops
  let picked : SExpr → SExpr := if picks.isEmpty then id else pickOverloads ovs picks sel
  let pk (m : MFn) : MFn :=
    { m with body := picked m.body, params := m.params.map fun sp => { sp with default := sp.default.map picked } }
  ((multiCandidates tops).filter (!ovs.contains ·.1)).map (fun (n, m) => (n, pk m)) ++
    ovs.flatMap fun f => (overloadsOf tops f).filterMap fun (k, _, m) =>
      if m.fx.contains "suspends" then none else some (k, pk m)

/-- The name of the function a method `m` of class `c` with several values
    becomes (#283). -/
def methodFnName (c m : String) : String := s!"{c}${m}"

/-- A method's body with the names of its class's members qualified by
    `Self` (#283): `isMethod`, `isMember` and `free` say which names. -/
partial def qualMembers (isMethod isMember free : String → Bool) (e : SExpr) : SExpr :=
  let go := qualMembers isMethod isMember free
  mapE (fun
    | .app p (.ident q n) args br =>
      if free n && isMethod n then some (.app p (.member q (.ident q "Self") n) (args.map go) br) else none
    | .ident p n => if free n && isMember n then some (.member p (.ident p "Self") n) else none
    | _ => none) e

/-- `e` with the calls of `names`, by name or as a member, as calls of
    `$h`: what is left of the names is then a use as a value (#283). -/
partial def eraseCallHeads (names : List String) (e : SExpr) : SExpr :=
  let go := eraseCallHeads names
  mapE (fun
    | .app p (.ident q x) args br => if names.contains x then some (.app p (.ident q "$h") (args.map go) br) else none
    | .app p (.member q r x) args br =>
      if names.contains x then some (.app p (.ident q "$h") ((r :: args).map go) br) else none
    | _ => none) e

/-- Whether two written types are the same as written. -/
partial def styEq : STy → STy → Bool
  | .name a, .name b => a == b
  | .arr a, .arr b | .opt a, .opt b => styEq a b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).all fun (x, y) => styEq x y
  | .map a b, .map c d => styEq a c && styEq b d
  | .app f as, .app g bs => f == g && as.length == bs.length && (as.zip bs).all fun (x, y) => styEq x y
  | .fn as e r, .fn bs e' r' =>
    as.length == bs.length && (as.zip bs).all (fun (x, y) => styEq x y) &&
      e.all e'.contains && e'.all e.contains && styEq r r'
  | _, _ => false

/-- A written type with `string` spelled `[]char`, which it is. -/
partial def styNorm : STy → STy
  | .name "string" => .arr (.name "char")
  | .arr a => .arr (styNorm a)
  | .opt a => .opt (styNorm a)
  | .tup ts => .tup (ts.map styNorm)
  | .map k v => .map (styNorm k) (styNorm v)
  | .app f ts => .app f (ts.map styNorm)
  | .fn ps e r => .fn (ps.map styNorm) e (styNorm r)
  | t => t

/-- A written type, for messages. -/
partial def styShow : STy → String
  | .name a => a.replace "::" "."
  | .arr a => "[]" ++ styShow a
  | .opt a => "?" ++ styShow a
  | .tup ts => "tuple(" ++ ", ".intercalate (ts.map styShow) ++ ")"
  | .map k v => "[" ++ styShow k ++ "]" ++ styShow v
  | .app f ts => f.replace "::" "." ++ "(" ++ ", ".intercalate (ts.map styShow) ++ ")"
  | .fn ps e r => "type{_(" ++ ", ".intercalate (ps.map (":" ++ styShow ·)) ++ ")" ++
      String.join (e.map (s!"<{·}>")) ++ ":" ++ styShow r ++ "}"

/-- A method with several values and its overrides (#283): the class that
    declares it, and the classes with an implementation (the declaring one
    first, unless abstract). `direct`: one implementation, the declaring
    class's, overridden nowhere: a plain call of its function. -/
structure MFam where
  root : String
  impls : List String
  direct : Bool
  /-- The declaring class's return type, before static receiver selection. -/
  ret : Option STy := none
  /-- The declaring class's parameters, whose types a dispatch's arguments
      are bound at. -/
  params : List SParam := []
  /-- (#283) The declaring class's type parameters, when it is generic: the
      dispatch's receiver then takes its type from the call, and the casts
      to each implementing class infer theirs from it. -/
  rootTps : List TParam := []
  /-- The method's own type parameters, inferred from its call arguments. -/
  methodTps : List TParam := []
  /-- Dispatch casts may refine or open the receiver's type arguments. -/
  refining : Bool := false
  /-- The static receiver's declaration determines a possibly narrower result. -/
  covariant : Bool := false
  /-- Concrete class tests paired with the implementation they inherit. -/
  cases : List (String × String) := []
  deriving Inhabited

/-- Source hierarchy data needed to rewrite one typed copied method call.
    The implementations travel through the ordinary retained-template pipeline. -/
structure CopiedMethods where
  families : List (String × MFam) := []
  ancestors : List (String × List String) := []
  interfaces : List String := []
  views : List ((String × String) × List (String × STy)) := []
  roots : List (String × List String) := []
  deriving Inhabited

def CopiedMethods.names (methods : CopiedMethods) : List String :=
  (methods.families.map fun (slot, _) => (slot.splitOn "$ov").headD slot).eraseDups

/-- The roots of a method's families (`roots`: the classes and interfaces
    that declare it without `<override>`) that a use `R.M` at `q` reaches,
    in the body of class `inC` (#283). When one declares it, that one,
    whatever `R` is. When several do apart, each is the root of a family of
    its own, and the receiver's class tells which: `Self`'s is the
    enclosing class; any other receiver's is the class an earlier
    elaboration found it of, whose root it noted by `q` (`picks`). The code
    at `q` may be elaborated at several receiver types (the clauses after a
    choice whose values are of different types, copied for each, #335): then
    each root noted. A receiver of no class (`""`: of a type parameter, those
    clauses shared, or one no elaboration reached) may be of any of them.
    None before that elaboration. -/
def rootsAt (anc : String → List String) (roots : List String) (picks : List (Pos × String))
    (inC : Option String) (q : Pos) (recv : SExpr) : List String :=
  if roots.length ≤ 1 then roots else
  match recv, inC with
  | .ident _ "Self", some d => roots.filter (anc d).contains
  | _, _ =>
    let noted := picks.filterMap fun (q', r) => if q' == q then some r else none
    if noted.contains "" then roots else roots.filter noted.contains

/-- (#283) The body a method of a family with several values keeps in its
    class, where the elaborator still checks it as a member, while its
    implementation is a function and each call of it is rewritten. It is
    elaborated as `Err()`, and `elabProgramCore` gives out no program in
    which a function calls one (`TyEnv.familyStubs`). -/
def familyStub (p : Pos) : SExpr := .app p (.ident p "$familyStub") [] false

/-- Whether `e` is a family's stub (`familyStub`). -/
def isFamilyStub : SExpr → Bool
  | .app _ (.ident _ "$familyStub") [] false => true
  | _ => false

/-- A method's name as a qualified call writes it (`(c:)M`, #125): `c` and
    `M`; `M` alone otherwise. -/
def qualified (m : String) : Option String × String :=
  match m.startsWith "(", (m.drop 1).toString.splitOn ":)" with
  | true, [c, m'] => (some c, m')
  | _, _ => (none, m)

/-- The calls of the methods of `fams` in `e` (#283), `inC` the class whose
    body this is (`anc` gives a class's ancestors, nearest first), each of
    the families of the roots `rootsAt` gives (`roots`, `picks`):
    - `R.M(args)` is a call of `M`'s function with `R` first. With
      overrides, it dispatches on the receiver's class: `$dispatch(root$M,
      block{ $r : root := $arg; $a… := $arg; $kv := $excl(…) }, R, args…)`,
      which `inlineCalls` makes an inlined call (its names tagged for the
      site): the receiver and the arguments bound once, as at a call, then
      an exclusive choice (#314) with an alternative per implementation `D`,
      guarded by `$d := D[$r]; not E[$r] …`, of value `D$M($d, …)`. It holds
      when `$r` is a `D` and no class `E` below `D` implements `M` (the casts
      are from the root, so always possible): exactly one holds, the one
      dynamic dispatch picks. Being exclusive, it is no generator in a
      `for`: what came before the call rolls back as at a call, unless the
      implementation reaches a choice of its own.
      Families with fixed/repeated/added type arguments instead use native
      cast conditionals over `MFam.cases`, so each selected implementation
      retains its refinement and opened arguments. `$methodCast` lets typed
      consumers discard impossible cases; `$methodMiss` supplies no values.
      A covariant family first saves the actual receiver, before its root
      view is bound, and records its static declaration's result type.
      Exact class cases can then omit implementations outside that view.
      With `trial`, it is a call of `root$M$fam` instead, for the fixpoint.
    - `R.M(args)` that reaches several roots (`rootsAt`) is the receiver
      bound once, then a case per root, `if ($d := $methodCast(root[$r]))
      then … else …`, of value that root's family's call (above) with `$d`
      for `R`, or `$d.M(args)` as written where the root's `M` has one
      value: the receiver's class picks the case, which its type tells
      where the code is elaborated (each copy of the clauses after a choice
      whose values are of different classes, #335: the elaborator drops the
      others, `pruneMethodCases`). The arguments are evaluated in the case.
    - `M(args)` in the body of a class below the root is `Self.M(args)`.
    - `(super:)M(args)` is a call of the nearest implementation above.
    - `R.(c:)M(args)` (#125) is a call in the family of the root `c` is
      below.
    A call's `M` is the method it calls, `slotsAt` its place and the name as
    written: of an overloaded method, the list the call takes (`M$ovK`), an
    earlier elaboration found, none before; where the call is elaborated at
    receivers of several hierarchies, each one's list (`R.M(args)` then
    reaches the roots of each). -/
partial def rwFamCalls (anc : String → List String) (fams : List (String × MFam)) (trial : Bool)
    (inC : Option String) (e : SExpr) (isIface : String → Bool := fun _ => false)
    (typeView : String → String → List (String × STy) := fun _ _ => [])
    (roots : String → List String := fun _ => []) (picks : List (Pos × String) := [])
    (slotsAt : Pos → String → List String := fun _ m => [m]) : SExpr :=
  let rw := fun x => rwFamCalls anc fams trial inC x isIface typeView roots picks slotsAt
  let below (f : MFam) (d : String) : List String := f.impls.filter fun x => x != d && (anc x).contains d
  -- (#375's review) an interface's default yields to every class's own
  -- implementation, as dispatch gives: a class's chain wins over the
  -- defaults of the interfaces it lists
  let yieldsTo (f : MFam) (d : String) : List String :=
    if isIface d then (below f d ++ f.impls.filter fun x => x != d && !isIface x).eraseDups else below f d
  -- (the implementations `(super:)` reaches, nearest first: the class's
  -- chain, then its interfaces, a derived one before those above it)
  let superOrder (d : String) : List String :=
    let ancs := (anc d).drop 1
    ancs.filter (!isIface ·) ++ (ancs.filter isIface).mergeSort fun a b => (anc a).length ≥ (anc b).length
  -- (a super call of one implementation's function, the receiver first:
  -- normalize its tuple before recursive calls become $rec/$recTo edges;
  -- one tuple argument to several positional
  -- parameters, and no named one, taken apart after the receiver, as at a
  -- call, #140, also where the function is not inlined, a kept body)
  let superCall (p q : Pos) (fn : String) (f : MFam) (recv : SExpr) (args : List SExpr) (br : Bool)
      (view : List (String × STy)) : SExpr :=
    -- A method's own parameters are inferred at this call. The ancestor's
    -- names are outside the override's scope; generic inlining (and lazy
    -- recursive binding) expands its tuple at the inferred instance.
    if !f.methodTps.isEmpty then .app p (.ident q fn) (recv :: args) br else
    let named := fun | SExpr.decl _ n _ _ _ => n.startsWith "?" | _ => false
    -- A super call is written in the caller class's type scope. Its
    -- invariant parameter types are the root signature viewed there,
    -- including renamed, fixed and compound inherited arguments.
    let posPs := (f.params.filter (!·.named)).map fun sp => { sp with ty := sp.ty.substNames view }
    match args with
    | [a] =>
      if named a || posPs.length < 2 then .app p (.ident q fn) (recv :: args) br else
      let site := s!"{p.line}_{p.col}"
      let (r, t) := (s!"$r{site}", s!"$t{site}")
      .block p [.decl p r none false recv, .decl p t (some (.tup (posPs.map (·.ty)))) false a,
        .app p (.ident q fn) (.ident p r :: posPs.zipIdx.map fun (_, i) => .app p (.ident p t) [.int p (i : Int)] false) br]
    | _ => .app p (.ident q fn) (recv :: args) br
  let call (p q : Pos) (m : String) (f : MFam) (recv : SExpr) (args : List SExpr) (br : Bool) : SExpr :=
    let named := fun | SExpr.decl _ n _ _ _ => n.startsWith "?" | _ => false
    let args := if !f.methodTps.isEmpty && (f.params.filter (!·.named)).length >= 2 then
        match args.filter (!named ·) with
        | [.tuple _ fields] =>
          if fields.length == (f.params.filter (!·.named)).length then fields ++ args.filter named else args
        | _ => args
      else args
    if f.direct then .app p (.ident q (methodFnName f.root m)) (recv :: args) br
    else if trial then .app p (.ident q (methodFnName f.root m ++ "$fam")) (recv :: args) br
    -- (its declaring class's the only implementation, an abstract override
    -- below it: that one, which dispatch always picks)
    else if f.impls == [f.root] && !f.covariant then .app p (.ident q (methodFnName f.root m)) (recv :: args) br
    else
      -- (names of this call's own, `inlineCalls` tags them for each site)
      let site := s!"{p.line}_{p.col}"
      let (r, dn, kv) := (s!"$r{site}", s!"$d{site}", s!"$kv{site}")
      let raw := s!"$receiver{site}"
      let keepStatic := f.covariant || !f.methodTps.isEmpty
      let actual := if keepStatic then SExpr.ident p raw else recv
      let aN (i : Nat) : String := s!"$a{i}_{site}"
      -- (the arguments as a call evaluates them: positional, then named as
      -- written, #283)
      let named := fun | SExpr.decl _ n _ _ _ => n.startsWith "?" | _ => false
      let args := args.filter (!named ·) ++ args.filter named
      let vals := args.map fun | a@(.decl _ n _ _ x) => if n.startsWith "?" then x else a | a => a
      let posPs := f.params.filter (!·.named)
      -- (one tuple argument to several positional parameters, and no named
      -- one: taken apart, as at a call, #140)
      let namedArgs := args.filter named
      let tupled := (args.filter (!named ·)).length == 1 && posPs.length ≥ 2
      let passed := if tupled then
        posPs.zipIdx.map (fun (_, i) => SExpr.ident p (aN i)) ++ namedArgs.zipIdx.map (fun (a, i) => match a with
          | .decl ap n t v _ => SExpr.decl ap n t v (.ident p (aN (posPs.length + i)))
          | _ => a)
        else
        args.zipIdx.map fun (a, i) => match a with
        | .decl ap n t v _ => if n.startsWith "?" then SExpr.decl ap n t v (.ident p (aN i)) else .ident p (aN i)
        | _ => .ident p (aN i)
      -- (each argument at its parameter's written type, as at a call: so
      -- `array{}` or `false` has the type it needs)
      -- (a generic family's, #283: the declaring class's type parameters
      -- named for this call, `$params` below inferring them from the
      -- receiver and the arguments, as at a call of a generic function)
      let tpN (n : String) : String := s!"$tp{p.line}x{p.col}_{n}"
      let tps := f.rootTps ++ f.methodTps
      let σn : List (String × String) := tps.map fun tp => (tp.name, tpN tp.name)
      let tyR (t : STy) : STy := styRename σn t
      let tyAt0 (a : SExpr) (i : Nat) : Option STy := match a with
        | .decl _ n _ _ _ =>
          if n.startsWith "?" then (f.params.find? fun (sp : SParam) => sp.name == (n.drop 1).toString).map fun (sp : SParam) => sp.ty
          else (posPs[i]?).map fun (sp : SParam) => sp.ty
        | _ => (posPs[i]?).map fun (sp : SParam) => sp.ty
      let tyAt (a : SExpr) (i : Nat) : Option STy := (tyAt0 a i).map tyR
      let binds : List SExpr := if tupled then
          let t := s!"$t{site}"
          SExpr.decl p t (some (tyR (.tup (posPs.map (·.ty))))) false (.ident p "$arg") ::
            (namedArgs.zipIdx.map (fun (a, i) => SExpr.decl p (aN (posPs.length + i)) (tyAt a (posPs.length + i)) false (.ident p "$arg"))) ++
            posPs.zipIdx.map fun (sp, i) => SExpr.decl p (aN i) (some (tyR sp.ty)) false (.app p (.ident p t) [.int p (i : Int)] false)
        else args.zipIdx.map fun (a, i) => SExpr.decl p (aN i) (tyAt a i) false (.ident p "$arg")
      let castTo (d : String) : SExpr := .app p (.ident p d) [if keepStatic then .ident p raw else .ident p r] true
      let alt (d : String) : List SExpr × SExpr :=
        let guard := if d == f.root then SExpr.decl p dn none false (.ident p r)
          else .decl p dn none false (castTo d)
        let nots := (yieldsTo f d).map fun x => SExpr.notE p (castTo x)
        (guard :: nots, .app p (.ident q (methodFnName d m)) (.ident p dn :: passed) br)
      let recvB : SExpr := .decl p r (some (if f.rootTps.isEmpty then .name f.root
        else .app f.root (f.rootTps.map fun tp => .name (tpN tp.name)))) false (.ident p "$arg")
      -- (a generic family's receiver and arguments bound together, their
      -- type arguments inferred as at a call, `$params`, #283: so the
      -- receiver is at the declaring class, and `false` or `array{}` at
      -- its parameter's type; a tuple argument's parts after)
      -- (the binding of the arguments, `bindParams`, groups them so when
      -- the template is led by `$tparams`, as an inlined generic call's;
      -- its name for messages only, as shown: no function's, which a use
      -- as a value would be taken for)
      let head : List SExpr := if tps.isEmpty then recvB :: binds else
        .app p (.ident p "$tparams") (.ident p (shownFnName (methodFnName f.root m)) ::
          tps.map fun tp => (tp.rename σn).marker p) false :: recvB :: binds
      -- A refining implementation must keep its cast with its body. Most
      -- specific classes win before interface defaults, as ordinary dispatch
      -- does. A marked cast lets typing discard statically impossible cases.
      let cases := if !f.refining && !keepStatic then mkExcl p (f.impls.map alt) else
        let fallback := if f.impls.contains f.root && !keepStatic then
          SExpr.app p (.ident q (methodFnName f.root m)) (.ident p r :: passed) br
          else .app p (.ident p "$methodMiss") [] false
        f.cases.foldr (fun (d, impl) rest =>
          let dn := dn ++ "$" ++ d
          let body := SExpr.app p (.ident q (methodFnName impl m)) (.ident p dn :: passed) br
          if d == f.root && !keepStatic then
            SExpr.block p [.decl p dn none false (.ident p r), body]
          else SExpr.ite p [.decl p dn none false (.app p (.ident p (if keepStatic then "$methodCase" else "$methodCast")) [castTo d] false)] body (some rest)) fallback
      let ret := if f.covariant then some (STy.app "$methodResult" [.name raw]) else f.ret.map tyR
      let ownTypes := f.methodTps.zipIdx.map fun (tp, i) =>
        SExpr.decl p s!"$methodTypeArg{i}" (some (.name (tpN tp.name))) false (.tuple p [])
      -- A statically selected implementation's omitted defaults may infer
      -- method parameters. Probe ordinary binding after supplied arguments
      -- are saved; its defaults still run only in the selected body.
      let inferTypes := if f.methodTps.isEmpty then [] else
        [SExpr.app p (.ident p "$methodParams") [.ident p raw, .str p [.text m], .block p ownTypes, .block p passed] br]
      let resultType := if !f.covariant then [] else
        [SExpr.app p (.ident p "$methodType") [.ident p raw, .str p [.text m], .block p ownTypes] false]
      let tmpl := head ++ inferTypes ++ resultType ++ [.decl p kv ret false cases]
      let dispatch := SExpr.app p (.ident p "$dispatch") (.ident q (methodFnName f.root m) :: .block p tmpl :: actual :: vals) false
      if !keepStatic then dispatch else
        .block p [.decl p raw none false recv, dispatch]
  -- (a use that reaches several roots, each's family or `M` as written, of
  -- the list it takes there: the receiver bound once, then a case per
  -- root; named for the first family's function, whose effects every
  -- case's caller allows, as the function has that case too)
  let across (p q : Pos) (cases : List (String × String × Option MFam)) (recv : SExpr)
      (args : List SExpr) (br : Bool) : SExpr :=
    let site := s!"{p.line}_{p.col}"
    let (r, kv) := (s!"$rr{site}", s!"$rk{site}")
    let arm (x : (String × String × Option MFam) × Nat) (rest : SExpr) : SExpr :=
      let ((root, slot, f), i) := x
      let d := s!"$rd{i}_{site}"
      let body := match f with
        | some f => call p q slot f (.ident p d) args br
        | none => .app p (.member q (.ident p d) slot) args br
      .ite p [.decl p d none false (.app p (.ident p "$methodCast") [.app p (.ident p root) [.ident p r] true] false)]
        body (some rest)
    let g := (cases.findSome? fun (_, slot, f) => f.map (methodFnName ·.root slot)).getD "$methodMiss"
    let cases := cases.zipIdx.foldr arm (.app p (.ident p "$methodMiss") [] false)
    .app p (.ident p "$dispatch") [.ident q g, .block p [.decl p r none false (.ident p "$arg"), .decl p kv none false cases], recv] false
  mapE (fun
    | .app p (.member q recv m0) args br => do
      let (within, m0) := qualified m0
      let slots := slotsAt p m0
      let m ← slots.head?
      match recv, inC, within with
      | .ident _ "(super:)", some d, _ =>
        -- (the nearest implementation above `d` of a family of `m`: of
        -- `d`'s own, the only one above it)
        let impl := (superOrder d).findSome? fun a => (fams.find? fun (x, f) => x == m && f.impls.contains a).map (a, ·.2)
        impl.map fun (a, f) => superCall p q (methodFnName a m) f (.ident q "Self") (args.map rw) br (typeView d f.root)
      | _, _, some c =>
        ((fams.find? fun (x, f) => x == m && (anc c).contains f.root).map (·.2)).map fun f =>
          call p q m f (rw recv) (args.map rw) br
      | _, _, none =>
        -- (the roots each list reaches: all of one no family of which is
        -- selected, whose cases are as written; none yet while a selected
        -- family's pick is to be made, the use as written for that round)
        let reach (s : String) : Option (List String) :=
          if (roots s).length ≤ 1 || !fams.any (·.1 == s) then some (roots s) else
          match rootsAt anc (roots s) picks inC q recv with
          | [] => none
          | rs => some rs
        let reached ← slots.mapM reach
        let cases := (slots.zip reached).flatMap fun (s, rs) => rs.map fun r =>
          (r, s, (fams.find? fun (x, f) => x == s && f.root == r).map (·.2))
        match cases with
        | [(_, s, some f)] => some (call p q s f (rw recv) (args.map rw) br)
        | _ =>
          if cases.all (·.2.2.isNone) then none else
          let receiver := rw recv
          let arguments := args.map rw
          let lowered := across p q cases receiver arguments br
          if trial then some lowered else
            some (.app p (.ident p "$producerAnchor")
              [.app p (.member q receiver m0) arguments br, lowered] false)
    | .app p (.ident q m) args br => do
      let d ← inC
      let m ← (slotsAt p m).head?
      ((fams.find? fun (x, f) => x == m && (anc d).contains f.root).map (·.2)).map fun f =>
        call p q m f (.ident q "Self") (args.map rw) br
    | _ => none) e

/-- Preserve the lexical owner and receiver of super calls left after
    selected multi-value families have been rewritten. These may call an
    ordinary scalar or overloaded method that stays in its class. -/
partial def sourceSuperCalls (c method : String) (e : SExpr) : SExpr :=
  mapE (fun
    | e@(.app _ (.ident _ "$sourceSuper") _ false) => some e
    | .app p f@(.member _ (.ident _ "(super:)") _) args br =>
      some (.app p (.ident p "$sourceSuper")
        [.str p [.text c], .str p [.text method], .ident p "Self",
          .app p f (args.map (sourceSuperCalls c method)) br] false)
    | _ => none) e

/-- The uses `R.M` in `e`, calls and values: where the call is (none for a
    value), where `R.M` is, `R` and `M`. -/
partial def memberUses (e : SExpr) : List (Option Pos × Pos × SExpr × String) :=
  match e with
  | .app p (.member q r m) as _ => (some p, q, r, m) :: (r :: as).flatMap memberUses
  | .member q r m => (none, q, r, m) :: e.children.flatMap memberUses
  | _ => e.children.flatMap memberUses

def copiedOverloadUses (code : SExpr) : List (Pos × String) :=
  callUses code ++ (memberUses code).filterMap fun (call, _, _, name) =>
    call.map (·, (qualified name).2)



/-- Rewrite only the list selected in this typed copy. Other lists are not
    guessed from a global first pick; existing family dispatch binds operands. -/
def CopiedMethods.rewrite (methods : CopiedMethods) (inC : Option String)
    (picks familyPicks : List (Pos × String)) (code : SExpr) : SExpr :=
  let slots (p : Pos) (written : String) :=
    if methods.names.contains written then
      (picks.filterMap fun (q, slot) => if p == q then some slot else none).eraseDups
    else [written]
  rwFamCalls (fun c => (methods.ancestors.lookup c).getD [c]) methods.families false inC code
    methods.interfaces.contains (fun c r => (methods.views.lookup (c, r)).getD [])
    (fun name => (methods.roots.lookup name).getD []) familyPicks slots

/-- Methods with several values (#283), as top-level functions that take
    `Self` explicitly, so that everything functions with several values
    have applies: `C$M($Self:C, params…)`, its body with the names of `C`'s
    members (and its supers') qualified by `Self`, then `Self` renamed;
    `R.M(args)` becomes `C$M(R, args)` (the receiver first, once), and in
    `C`'s bodies and its subclasses' `M(args)` and `Self.M(args)` become
    `C$M(Self, args)`. Each class or interface that declares `M` without
    `<override>` is the root of a family of its own, the declarations of
    `M` below it. Inlining has no types, so when one root declares `M`,
    `R.M` names its family whatever `R` is; when several do, `R.M` names
    the family of the root `R`'s class is below, which an earlier
    elaboration noted by the place of `R.M` (`picks`, `rootsAt`), or, where
    that place is elaborated at receivers of several classes, a case for
    each (`rwFamCalls`). The uses
    not picked yet are returned with the program, for the elaboration to
    note; they stay as written until then. Such a method's name is no
    field, enumerator or member of a built-in type, no top-level name and
    no parameter or local. Class parameters become function parameters,
    followed by the method's own type parameters. Suspension remains
    unsupported. Selected families keep stubs in their classes for
    ordinary signature/override validation.
    Each list of an overloaded method (#106) is a method of its own, as the
    elaborator names it (`M$ovK`, `MethodOverloads`), a family's method
    one of them; a call's, the one an earlier elaboration found it takes,
    noted by the call's place (`overloadPicks`). The calls not picked yet
    of a method with a list that has several values are returned too, for
    the elaboration to note; they stay as written until then. -/
def methodFns (tops : List STop) (reserved : List String := []) (picks : List (Pos × String) := [])
    (overloadPicks : List (Pos × String) := []) :
    Except String (List STop × List (Pos × String) × List (Pos × String) × CopiedMethods) := do
  let classes := tops.filterMap fun
    | .classDef _ n _ tps _ pa ii fs ms => some (n, (pa, ii, fs, ms, tps))
    | _ => none
  if classes.isEmpty then return (tops, [], [], {})
  -- (#106) a method declaration's name is its list's (`M$ovK`) if its name
  -- is overloaded; a call's, the list picked for it, none before
  let mo := MethodOverloads.of tops
  let overloaded (m : String) : Bool := mo.lists.any (·.1.2 == m)
  let slotOf (c : String) : STop → STop
    | .fn p m ps mtps fx r b =>
      let ctps := ((classes.lookup c).map (·.2.2.2.2)).getD []
      .fn p (mo.name c m ctps mtps ps (fx.contains "override") none) ps mtps fx r b
    | d => d
  -- (the lists an earlier elaboration found a call takes, none before: one
  -- per hierarchy the receiver is of where the call is elaborated at
  -- several, #335)
  let slotsAt (p : Pos) (m : String) : List String :=
    if overloaded m then ((overloadPicks.filter (·.1 == p)).map (·.2)).filter (· != "") |>.eraseDups else [m]
  let slotAt (p : Pos) (m : String) : Option String := (slotsAt p m).head?
  -- (a method's name as written, for messages)
  let written (n : String) : String := (n.splitOn "$ov").headD n
  let parentNames (pa : List STy) : List String := pa.filterMap fun | .name n => some n | .app n _ => some n | _ => none
  let rec ancestors (fuel : Nat) (c : String) : List String := match fuel with
    | 0 => [c]
    | f + 1 => c :: (((classes.lookup c).map fun (pa, _) => (parentNames pa).flatMap (ancestors f)).getD [])
  let anc (c : String) : List String := (ancestors (classes.length + 1) c).eraseDups
  -- (every member name of `c`, inherited ones too)
  let members (c : String) : List String := (anc c).flatMap fun d =>
    match classes.lookup d with
    | some (_, _, fs, ms, _) => fs.map (·.1) ++ ms.filterMap fun | .fn _ m .. => some m | _ => none
    | none => []
  -- (struct fields and enumerators too, and the members of built-in types
  -- and of the prelude, `reserved`: `R.M` may be any of them)
  let allFields : List String := classes.flatMap (fun (_, (_, _, fs, _, _)) => fs.map (·.1)) ++
    tops.flatMap (fun
      | .const _ _ _ _ (.structDef _ _ _ fs) => fs.map (·.1)
      | .const _ _ _ _ (.enumDef _ vs _) => vs
      | _ => []) ++ reserved
  let topNames : List String := tops.filterMap fun | .fn _ n .. | .const _ n .. | .classDef _ n .. => some n
  let localBinders : List String := tops.flatMap fun
    | .fn _ _ ps _ _ _ b => ps.map (·.name) ++ localsOf b
    | .classDef _ _ _ _ _ _ _ _ ms => ms.flatMap fun | .fn _ _ ps _ _ _ b => ps.map (·.name) ++ localsOf b | _ => []
    | _ => []
  -- (every declaration of each method name: class, method)
  let decls : List (String × STop) := classes.flatMap fun (c, (_, _, _, ms, _)) => ms.filterMap fun
    | m@(.fn _ n ..) => if n.startsWith "$" || n.startsWith "(" then none else some (c, slotOf c m)
    | _ => none
  let names : List String := (decls.filterMap fun | (_, .fn _ n ..) => some n | _ => none).eraseDups
  let declsOf (n : String) : List (String × STop) := decls.filter fun | (_, .fn _ x ..) => x == n | _ => false
  let isOverride : STop → Bool := fun | .fn _ _ _ _ fx _ _ => fx.contains "override" | _ => false
  let isAbstract : STop → Bool := fun | .fn _ _ _ _ fx _ _ => fx.contains "$abstract" | _ => false
  -- (#283) the root's type parameters as class `c` sees them, through
  -- each parent's type arguments: `ibox := class(box(int))` sees `t` as
  -- `int`, so its override may write `int` where the root writes `t`
  let rec rootView (fuel : Nat) (c root : String) : Option (List (String × STy)) :=
    if c == root then some (((classes.lookup root).map fun (_, _, _, _, tps) => tps.map fun tp => (tp.name, STy.name tp.name)).getD [])
    else match fuel with
      | 0 => none
      | k + 1 => ((classes.lookup c).map (·.1)).getD [] |>.findSome? fun pe =>
          let (pn, args) : String × List STy := match pe with
            | .app pn args => (pn, args)
            | .name pn => (pn, [])
            | _ => ("", [])
          (rootView k pn root).map fun σp =>
            let ptps := ((classes.lookup pn).map fun (_, _, _, _, tps) => tps.map (·.name)).getD []
            σp.map fun (r, t) => (r, t.substNames (ptps.zip args))
  -- (the classes and interfaces that declare `n` without <override>: each
  -- the root of a family of its own, the declarations below it)
  let rootsOf (n : String) : List String := ((declsOf n).filter fun (_, m) => !isOverride m).map (·.1)
  -- (a name several of them declare apart: the family of a use `R.n` is
  -- that of the root `R`'s class is below, which types tell, `rootsAt`)
  let shared (n : String) : Bool := (rootsOf n).eraseDups.length > 1
  -- (the declarations of `n` below root `r`, and those below no root)
  let famDecls (n r : String) : List (String × STop) :=
    (declsOf n).filter fun (c, _) => (anc c).contains r || !(rootsOf n).any (anc c).contains
  let shown (c : String) : String := c.replace "::" "."
  -- (why the declarations of `n` below root `r` cannot become functions,
  -- if they cannot: `r` declares it, the others below it override it, and
  -- no class below `r` is below another root)
  -- (and, for a reason of one declaration's own, its class)
  let whyNot (n r : String) : Option (String × Option String) := Id.run do
    let rs := rootsOf n
    if rs.isEmpty then return some (s!"no class declares {written n} without <override>", none)
    -- (another declaration without <override> in `r`, above it or below
    -- it: an overload, or one missing its <override>, which the elaborator
    -- says)
    let kin := (declsOf n).filter fun (c, m) => !isOverride m && ((anc c).contains r || (anc r).contains c)
    if kin.length > 1 then
      let sig : STop → List STy := fun | .fn _ _ ps .. => ps.map (styNorm ·.ty) | _ => []
      let same := kin.all fun (_, m) => kin.all fun (_, m') =>
        (sig m).length == (sig m').length && ((sig m).zip (sig m')).all fun (x, y) => styEq x y
      return some (if same then "" else s!"{written n} is overloaded", none)
    -- (a class below `r` and another root: a slot of each, #70)
    for (c, _) in classes do
      if (anc c).contains r then
        if let some r' := rs.find? fun x => x != r && (anc c).contains x then
          return some (s!"{shown c} is below both {shown r} and {shown r'}, which each declare {written n} without <override>", none)
    let ds := famDecls n r
    for (c, m) in ds do
      let some _ := classes.lookup c | return some ("", none)
      -- (an interface's, #283: the dispatch's root, as a class's; its
      -- default implementation, if it gives one, the alternative for the
      -- classes that have none of their own, as a class's own is)
      if !(anc c).contains r then
        return some (s!"{shown c} overrides it without being below {" or ".intercalate (rs.eraseDups.map shown)}", none)
      if let .fn _ _ _ _ fx _ _ := m then
        -- (an override that is `<decides>` where the declaration is not, or
        -- the other way round: no family, for the elaborator's check of the
        -- override's signature to say so, not a call's brackets)
        let rootDecides := (ds.find? (·.1 == r)).any fun | (_, .fn _ _ _ _ rfx _ _) => rfx.contains "decides" | _ => false
        if fx.contains "decides" != rootDecides then return some ("", none)
        if fx.contains "suspends" then return some ("is <suspends>", some c)
    let n := written n
    if allFields.contains n || topNames.contains n || localBinders.contains n then
      return some (s!"{n} is also the name of a field, an enumerator, a member of a built-in type, a top-level name, a parameter or a local", none)
    return none
  -- (the families that may become functions)
  let fams : List (String × MFam) := names.flatMap fun n => (rootsOf n).eraseDups.filterMap fun root =>
    if (whyNot n root).isSome then none else
    let ds := famDecls n root
    let impls := (ds.filter fun (_, m) => !isAbstract m).map (·.1)
    let impls := (impls.filter (· == root)) ++ impls.filter (· != root)
    let ret := (ds.find? (·.1 == root)).bind fun | (_, .fn _ _ _ _ _ r _) => some r | _ => none
    let methodTps := ((ds.find? (·.1 == root)).bind fun | (_, .fn _ _ _ tps _ _ _) => some tps | _ => none).getD []
    let covariant := ds.any fun (c, m) => match ret, m with
      | some r0, .fn _ _ _ mtps _ r _ =>
        let σ := ((rootView (classes.length + 1) c root).getD []) ++
          (methodTps.zip mtps).map (fun (a, b) => (a.name, STy.name b.name))
        let r0c := r0.substNames σ
        c != root && !styEq (styNorm r) (styNorm r0c)
      | _, _ => false
    let params := ((ds.find? (·.1 == root)).bind fun | (_, .fn _ _ ps _ _ _ _) => some ps | _ => none).getD []
    let rootTps := ((classes.lookup root).map fun (_, _, _, _, tps) => tps).getD []
    let refining := ds.any fun (c, _) =>
      if c == root then false else
      let ctps := ((classes.lookup c).map fun (_, _, _, _, tps) => tps.map (·.name)).getD []
      match rootView (classes.length + 1) c root with
      | some σ =>
        let args := σ.map (·.2)
        !(args.all (fun | .name x => ctps.contains x | _ => false) &&
          ctps.all (fun x => args.any fun | .name y => y == x | _ => false) &&
          (args.filterMap fun | .name y => some y | _ => none).eraseDups.length == args.length &&
          (((classes.lookup c).map fun (_, _, _, _, tps) => tps).getD []).all fun tp =>
            tp.constraint != "comparable" || (rootTps.zip args).any fun (rp, arg) =>
              rp.constraint == "comparable" && (match arg with | .name x => x == tp.name | _ => false))
      | none => false
    let isIface (c : String) := ((classes.lookup c).map fun (_, ii, _) => ii).getD false
    let ordered := impls.mergeSort fun a b =>
      if isIface a != isIface b then !isIface a else (anc a).length ≥ (anc b).length
    let cases := classes.filterMap fun (c, (_, ii, _)) =>
      if ii || !(anc c).contains root then none else
      (ordered.find? (anc c).contains).map fun impl => (c, impl)
    let cases := cases.mergeSort fun a b => (anc a.1).length ≥ (anc b.1).length
    some (n, { root, impls, direct := impls == [root] && ds.length == 1, ret, params, rootTps, methodTps, refining, covariant, cases })
  -- (which of them are interfaces: their defaults yield to classes', #375)
  let isIfaceC (c : String) : Bool := match classes.lookup c with
    | some (_, ii, _, _, _) => ii
    | none => false
  let rw := fun fs trial inC e => rwFamCalls anc fs trial inC e isIfaceC
    (fun c root => (rootView (classes.length + 1) c root).getD []) (fun n => (rootsOf n).eraseDups) picks slotsAt
  -- (a method's body as the function's: its members qualified by `Self`,
  -- then `Self` the parameter `$Self`)
  let fnOf (fs : List (String × MFam)) (trial : Bool) (c : String) : STop → Option STop
    | .fn p m ps mtps fx r b =>
      let mem := members c
      let isMethodName := fun n => (anc c).any fun d => match classes.lookup d with
        | some (_, _, _, ms, _) => ms.any fun | .fn _ x .. => x == n | _ => false
        | none => false
      let bound := ps.map (·.name) ++ localsOf b
      let free := fun n => !bound.contains n && n != "Self"
      let qual := qualMembers isMethodName mem.contains free
      -- (now `M(…)` is `Self.M(…)`; then the calls of the selected ones;
      -- a parameter's default too, which sees the method's fields)
      let fix := fun e => renameE [("Self", "$Self")] (sourceSuperCalls c m (rw fs trial (some c) (qual e)))
      let ps' := ps.map fun sp => { sp with default := sp.default.map fix }
      -- (a generic class's type parameters the function's, `$Self` the
      -- class at them)
      let tps : List TParam := ((classes.lookup c).map fun (_, _, _, _, tps) => tps).getD []
      let selfTy : STy := if tps.isEmpty then .name c else .app c (tps.map fun tp => .name tp.name)
      some (.fn p (methodFnName c m) ({ name := "$Self", ty := selfTy } :: ps') (tps ++ mtps) fx r (fix b))
    | _ => none
  let implFns (fs : List (String × MFam)) : List STop := fs.flatMap fun (n, f) =>
    f.impls.filterMap fun c => ((declsOf n).find? (·.1 == c)).bind fun (_, m) => fnOf fs false c m
  -- (which have several values: with every family's calls rewritten, the
  -- functions' fixpoint; a family with overrides through `root$M$fam`,
  -- whose body calls each implementation)
  let famFns : List STop := fams.filterMap fun (n, f) =>
    if f.direct then none else
    match (declsOf n).find? (·.1 == f.root) with
    | some (_, .fn p _ ps mtps fx r _) =>
      let args := ps.map fun sp => SExpr.ident p sp.name
      let selfTy : STy := if f.rootTps.isEmpty then .name f.root else .app f.root (f.rootTps.map fun tp => .name tp.name)
      some (.fn p (methodFnName f.root n ++ "$fam") ({ name := "$Self", ty := selfTy } :: ps) (f.rootTps ++ mtps) fx r
        (.tuple p (f.impls.map fun c => .app p (.ident p (methodFnName c n)) (.ident p "$Self" :: args) false)))
    | _ => none
  -- (parameters' defaults too, which a call evaluates)
  let rwPs (fs : List (String × MFam)) (trial : Bool) (inC : Option String) (ps : List SParam) : List SParam :=
    ps.map fun sp => { sp with default := sp.default.map (rw fs trial inC) }
  let rwTops (fs : List (String × MFam)) (trial : Bool) : List STop := tops.map fun
    | .fn p n ps tps fx r b => .fn p n (rwPs fs trial none ps) tps fx r (rw fs trial none b)
    | .const p n sp ty e => .const p n sp ty (rw fs trial none e)
    | .classDef p n nsp tps sp pa ii fs' ms =>
      .classDef p n nsp tps sp pa ii (fs'.map fun f => { f with default := f.default.map (rw fs trial (some n)) }) (ms.map fun
        | .fn p2 m ps fx2 x r b => .fn p2 m (rwPs fs trial (some n) ps) fx2 x r (rw fs trial (some n) b)
        | s => s)
  -- (in the trial, calls of the families go through `$fam`)
  let trialFns := fams.flatMap fun (n, f) =>
    f.impls.filterMap fun c => ((declsOf n).find? (·.1 == c)).bind fun (_, m) => fnOf fams true c m
  -- (and the calls of overloaded functions as `inlineMulti` takes them,
  -- `overloadCandidates`)
  let mv := multiValued (overloadCandidates (rwTops fams true ++ trialFns ++ famFns) overloadPicks fun _ => true)
  let pickedAll : SExpr → SExpr :=
    if overloadPicks.isEmpty then id else pickOverloads (overloadedFns tops) overloadPicks fun _ => true
  let famHas (n : String) (f : MFam) : Bool :=
    mv.contains (if f.direct then methodFnName f.root n else methodFnName f.root n ++ "$fam")
  -- (a method with several values whose declarations cannot become
  -- functions: refused, saying why)
  for n in names do
    for r in (if (rootsOf n).isEmpty then [""] else (rootsOf n).eraseDups) do
      if let some (why, atC) := whyNot n r then
        if why != "" then
          let multi := (famDecls n r).find? fun (c, m) => match m with
            | .fn _ _ _ _ _ _ b =>
              let b' := markCalls mv (pickedAll (rw fams true (some c) b))
              let ss := stmtsOf b'
              hasChoice ss || ss.any liftsHere || anyE (fun | .ret _ (some e) => hasLiftable e | _ => false) b'
            | _ => false
          if let some (c1, .fn p1 ..) := multi then
            match atC with
            | none => throw s!"{p1.show}: {shown c1}.{written n} has several values, but {why}: such methods are not supported yet (#283)"
            | some c0 =>
              -- (said of the declaration it is about, #328's review)
              let p0 := (((declsOf n).find? (·.1 == c0)).bind fun | (_, .fn q ..) => some q | _ => none).getD p1
              if c0 == c1 then
                throw s!"{p0.show}: {shown c0}.{written n} has several values, but it {why}: such methods are not supported yet (#283)"
              throw s!"{p0.show}: {shown c0}.{written n} {why}, and {shown c1}.{written n} has several values: such methods are not supported yet (#283)"
  let sel := fams.filter fun (n, f) => famHas n f
  -- (`(super:)M(…)` with nothing above implementing M: as the elaborator
  -- says, before the body leaves its class, #328's review)
  for (n, f) in sel do
    for (c, m) in famDecls n f.root do
      if let .fn q _ _ _ _ _ b := m then
        if anyE (fun | .app p (.member _ (.ident _ "(super:)") x) .. => slotAt p x == some n | _ => false) b &&
            (((anc c).drop 1).find? f.impls.contains).isNone then
          throw s!"{q.show}: nothing above {shown c} implements '{written n}'"
  if sel.isEmpty then return (tops, [], [], {})
  -- (a parameter or local named like a member: refused, as in the class,
  -- since the body leaves it)
  for (n, f) in sel do
    for c in f.impls do
      if let some (_, .fn p _ ps _ _ _ b) := (declsOf n).find? (·.1 == c) then
        let mem := members c
        if let some sp := ps.find? (mem.contains ·.name) then
          throw s!"{p.show}: parameter '{sp.name}' of {written n} is already a field or method of {c.replace "::" "."}; Verse does not allow shadowing"
        if let some (x, q) := (localDecls b).find? (mem.contains ·.1) then
          throw s!"{q.show}: '{x}' is already a field or method of {c.replace "::" "."}; Verse does not allow shadowing"
  -- (the program with those methods out of their classes and their calls
  -- rewritten, and their functions)
  let selNames := sel.map (·.1)
  -- (the selected family class `c`'s method `m` is of, if any)
  let selAt (c m : String) : Option MFam := (sel.find? fun (x, f) => x == m && (anc c).contains f.root).map (·.2)
  -- (each of a family with overrides stays in its class as a stub,
  -- `familyStub`, which no call reaches: so the elaborator still checks it
  -- as a member, <final>, its signature and effects against the one it
  -- overrides, an abstract one implemented)
  let stub (q : Pos) : SExpr := familyStub q
  -- (one overridden nowhere, `direct`, is taken out, as there is nothing
  -- to check it against, unless its name is `shared`, or overloaded in any
  -- hierarchy: a use the elaboration picks the family or list of then calls
  -- it as written, and the elaborator names an overloaded one's lists as
  -- here)
  let slotName (c : String) (d : STop) : String := match slotOf c d with
    | .fn _ m .. => m
    | _ => ""
  let out := (rwTops sel false).map fun
    | .classDef p n nsp tps sp pa ii fs ms =>
      .classDef p n nsp tps sp pa ii fs ((ms.filter fun
          | d@(.fn _ m ..) => let x := slotName n d; !(selAt n x).any (·.direct && !shared x && !overloaded m)
          | _ => true).map fun
        | d@(.fn p2 m ps tps2 fx r _) =>
          -- (an abstract one, or one with no body, as written)
          if (selAt n (slotName n d)).isNone || fx.contains "$abstract" then d
          else .fn p2 m (ps.map fun sp => { sp with default := sp.default.map fun d => stub d.pos }) tps2 fx r (stub p2)
        | s => s)
    | t => t
  -- (the bodies of a definition, each with the class it is in)
  let bodiesOf : STop → List (Option String × SExpr)
    | .fn _ _ ps _ _ _ b => (b :: ps.filterMap (·.default)).map (none, ·)
    | .const _ _ _ _ e => [(none, e)]
    | .classDef _ c _ _ _ _ _ fs ms => (fs.filterMap (·.default) ++ ms.flatMap fun
        | .fn _ _ ps _ _ _ b => b :: ps.filterMap (·.default)
        | _ => []).map (some c, ·)
  -- (what is left of their names is a use as a value: refused, as for a
  -- function's; a name of theirs is nothing else's, or one whose family
  -- the receiver's class gives, `rootsAt`)
  for t in out do
    for (inC, b) in bodiesOf t do
      let b := eraseCallHeads selNames b
      for (m, f) in sel do
        let use : SExpr → Bool := fun
          | .member q r x => x == m && (rootsAt anc (rootsOf m).eraseDups picks inC q r).contains f.root
          | .ident _ x => x == m && (!shared m || inC.any fun d => (anc d).contains f.root)
          | _ => false
        if anyE use b then
          let p := ((stmtsOf b).find? (anyE use)).map (·.pos) |>.getD b.pos
          throw s!"{p.show}: {shown f.root}.{written m} has several values, so it cannot be used as a function value (#235, #283)"
  -- (#283) the uses `R.M` of a `shared` name of a selected family that
  -- only `R`'s class can tell, not picked yet: the elaboration notes the
  -- root that class is below, for the next round (`Requests.families`)
  -- (a use of an overloaded name, of the list picked for it)
  let sites := (tops.flatMap bodiesOf).flatMap fun (inC, b) => (memberUses b).flatMap fun (cp, q, r, m) =>
    let (within, m) := qualified m
    let ms := match cp with
      | some p => slotsAt p m
      | none => if overloaded m then [] else [m]
    let byClass := within.isSome || match r, inC with
      | .ident _ "Self", some _ | .ident _ "(super:)", _ => true
      | _, _ => false
    ms.filter (fun m => shared m && selNames.contains m && !byClass && (picks.lookup q).isNone) |>.map (q, ·)
  -- (a call takes one list of a hierarchy's wherever it is elaborated: two
  -- of one class's, copies of the clauses after a choice whose values are
  -- of different types taking each by its arguments' types, #335, would
  -- need the arguments' types to pick the case, as the receiver's class
  -- picks the root's)
  let listShown (o : String) : String :=
    match (declsOf o).head? with
    | some (_, .fn _ _ ps ..) => s!"{written o}({", ".intercalate (ps.map (styShow ·.ty))})"
    | _ => written o
  for (p, o) in overloadPicks do
    if let some (_, o') := overloadPicks.find? fun (p', o') => p' == p && o' != o && o' != "" && o != "" then
      let declares (c o : String) : Bool := (declsOf o).any fun (d, _) => (anc c).contains d
      if (selNames.contains o || selNames.contains o') && classes.any fun (c, _) => declares c o && declares c o' then
        throw s!"{p.show}: this call takes {listShown o} in the clauses copied for one alternative of a choice and {listShown o'} in those copied for another, and which list of an overloaded method with several values a call takes is decided before types: not supported yet (#283); write the clauses after the choice apart for its alternatives, or give the lists names of their own"
  -- (#106) the calls of an overloaded method with a selected list whose
  -- list is not picked yet, `R.M(args)` or, in a class's body, `M(args)`:
  -- the elaboration notes the list each takes, for the next round
  -- (`Requests.overloads`)
  let methodsOf (c : String) : List String := (anc c).flatMap fun d => match classes.lookup d with
    | some (_, _, _, ms, _) => ms.filterMap fun | .fn _ m .. => some m | _ => none
    | none => []
  let pending (m : String) : Bool := overloaded m && sel.any fun (x, _) => written x == m
  let calls (inC : Option String) : SExpr → List (Pos × String) := fun b =>
    ((memberUses b).filterMap fun (cp, _, _, m) => cp.map (·, (qualified m).2)) ++
      match inC with
      | some c => (callUses b).filter fun (_, m) => (methodsOf c).contains m
      | none => []
  let ovSites := (tops.flatMap bodiesOf).flatMap fun (inC, b) =>
    (calls inC b).filter fun (p, m) => pending m && (overloadPicks.lookup p).isNone
  let copiedFamilies := sel.filter fun (slot, _) => overloaded (written slot)
  let copied : CopiedMethods := {
    families := copiedFamilies
    ancestors := classes.map fun (c, _) => (c, anc c)
    interfaces := classes.filterMap fun (c, (_, ii, _)) => if ii then some c else none
    views := classes.flatMap fun (c, _) => copiedFamilies.map fun (_, family) =>
      ((c, family.root), (rootView (classes.length + 1) c family.root).getD [])
    roots := copiedFamilies.map fun (slot, _) => (slot, (rootsOf slot).eraseDups) }
  return (out ++ implFns sel, sites, ovSites.eraseDups, copied)

end OpenVerse.Front.Choice
