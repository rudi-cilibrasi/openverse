/-
  OpenVerse front end — elaboration of surface Verse into Verse Core.

  * Names are resolved: locals to slots of the function's frame, functions
    and constants to program indices. Verse forbids shadowing; so does this.
  * Types are checked (int, logic, char, string = []char, []t, ?t, tuples,
    void), bidirectionally so that `false` and `array{}` take their type
    from context.
  * Failure discipline (Book of Verse ch. 8): an expression that can fail
    must be in a failure context — an `if` condition, a `for` clause,
    `option{}`, `logic{}`, `not`, the left of `or`, or a `<decides>`
    function body. "Can fail" is computed by `Expr.mayFail`, the very
    analysis the `<decides>` soundness theorem (`Eval.no_fail`) is about.
  * Derived forms use `OpenVerse.Core.Derived` (`not`, `or`, `option{}`,
    `logic{}`), whose rollback laws are proved.
  * The result is checked with `Prog.check` (proved to imply the hypotheses of
    the core theorems) before anyone runs it.
-/
import OpenVerse.Core.Show
import OpenVerse.Core.Check
import OpenVerse.Core.Derived
import OpenVerse.Core.TypeCheck
import OpenVerse.Core.Control
import OpenVerse.Front.Parser
import OpenVerse.Front.Profile
import OpenVerse.Front.Suspend
import OpenVerse.Front.Rational
import OpenVerse.Front.Modules
import OpenVerse.Front.FnValues
import OpenVerse.Front.Choice
import OpenVerse.Front.Refine
import OpenVerse.Front.FrameRefs
import OpenVerse.Front.SourceFrames
import OpenVerse.Front.FailCapture
import OpenVerse.Front.CompilerWrites
import OpenVerse.Front.Types
import Std.Data.HashMap

namespace OpenVerse.Front
open OpenVerse

/-- Whether `e` assigns a slot below `n` (#400): one it did not make. -/
partial def _root_.OpenVerse.Expr.assignsBelow (n : Nat) : Expr → Bool
  | .assign j e => j < n || e.assignsBelow n
  | .ret e | .loop e | .print e => e.assignsBelow n
  | .seq a b => a.assignsBelow n || b.assignsBelow n
  | .prim _ es | .heap _ es | .call _ es => es.any (·.assignsBelow n)
  | .ite c t e => c.assignsBelow n || t.assignsBelow n || e.assignsBelow n
  | .forE j it f b => j < n || it.assignsBelow n || f.assignsBelow n || b.assignsBelow n
  | _ => false

/-- Whether `e` prints or calls a function (which might), #243, #351: code
    whose effects a failure after it would have to undo. -/
partial def _root_.OpenVerse.Expr.printsOrCalls : Expr → Bool
  | .print _ | .call .. => true
  | .assign _ e | .ret e | .loop e => e.printsOrCalls
  | .seq a b => a.printsOrCalls || b.printsOrCalls
  | .prim _ es | .heap _ es => es.any (·.printsOrCalls)
  | .ite c t e => c.printsOrCalls || t.printsOrCalls || e.printsOrCalls
  | .forE _ it f b => it.printsOrCalls || f.printsOrCalls || b.printsOrCalls
  | _ => false

/-- A value that may go in a call's arguments in place of its temporary: a
    literal, a slot, or a tuple of those (`(1, 2)`, a default), which has no
    effect nor failure to keep in order. -/
partial def _root_.OpenVerse.Expr.pureArg : Expr → Bool
  | .lit _ | .local _ => true
  | .prim .mkTup es => es.all Expr.pureArg
  | _ => false

/-- Inline the pure argument temporaries around a dispatch call. Defaults
    are evaluated by a separate typed implementation helper. -/
partial def Expr.inlineArgTemps (e : Expr) : Option Expr :=
  let rec collect : Expr → Option (List (Nat × Expr) × Nat × List Expr)
    | .call f es => some ([], f, es)
    | .seq (.assign t v) rest =>
      if v.pureArg then (collect rest).map fun (ts, f, es) => ((t, v) :: ts, f, es) else none
    | _ => none
  let rec resolve (ts : List (Nat × Expr)) (fuel : Nat) (a : Expr) : Expr :=
    match fuel, a with
    | f + 1, .local t => match ts.lookup t with
      | some v => resolve ts f v
      | none => a
    | _, a => a
  (collect e).map fun (ts, f, es) => .call f (es.map (resolve ts (ts.length + 1)))

structure SourceStorage where
  frame : String
  name : String
  args : List Ty

def SourceStorage.subst (s : SourceStorage) (σ : List (String × Ty)) : SourceStorage :=
  { s with args := s.args.map (·.subst σ) }

structure Local where
  name    : String
  slot    : Nat
  ty      : Ty
  mutable : Bool
  storage : Option SourceStorage := none

/-- The heap effects (`<transacts>` allows all of them). -/

structure Sig where
  idx     : Nat
  name    : String
  params  : List Ty
  ret     : Ty
  decides : Bool
  isConst : Bool
  /-- The named parameters (the last ones of `params`): name and default. -/
  named   : List (String × Option SExpr) := []
  /-- Every parameter's name, in order: a named one's default may use those
      before it. -/
  pnames  : List String := []
  /-- A generic function's type parameters (name, declared comparable). Its
      `params` and `ret` mention them as `Ty.param`. Its Verse Core function
      takes one more hidden parameter per type parameter, after these: a
      value of that type (`witness`), from which its slots of that type are
      initialised (`slotDefault`). -/
  tparams : List (String × Bool) := []
  /-- The heap effects its specifiers allow (#35). -/
  fx : List String := heapFx
  /-- `<suspends>` (#156): lowered to a frame and a resume function. -/
  suspends : Bool := false
  /-- Of a method of a class with type parameters that its parent's type
      arguments do not give (#209): those type parameters, whose values it
      reads from its receiver's hidden fields (`$w.…`), not from hidden
      parameters, as a dispatch that opens them has none to pass. -/
  selfTps : List String := []
  /-- The class or interface whose scope its body and its named parameters'
      defaults resolve in, when not the one its name says: a class's copy of
      an interface's default, the interface (#53, `copyScope?`). -/
  scope : Option String := none
  deriving Inhabited

/-- How many hidden parameters (values of type arguments) a function takes. -/
def Sig.ndicts (s : Sig) : Nat := s.tparams.length - s.selfTps.length

/-- Default-dispatch helpers are private forwarding functions, with defaults
    evaluated in the selected implementation's own type context. -/
def defaultBridge (n : String) : Bool := (n.splitOn "$dispatchDefaults").length > 1

/-- Spawn adapters take every argument already bound, including defaults. -/
def spawnAdapter (n : String) : Bool := (n.splitOn "$spawnBody").length > 1

/-- A spawn factory is called only in its concrete class's tag case; its
    adapter keeps that same receiver. The singleton tag lets their hidden
    witness reads retain the class's exact field types. -/
def spawnParamTypes (env : TyEnv) (name : String) (types : List VTy) : List VTy :=
  if spawnAdapter name || (name.splitOn "$dispatchDefaultsSpawn").length > 1 then
    match types with
    | .ref _ args :: rest => .ref [env.tagOf ((name.splitOn ".").headD "")] args :: rest
    | _ => types
  else types

/-- Whether function `s` fits the closed function type `t` other than at its
    own types, as the value classes made for a type asked for do (#214, as
    `FnValues.desugar`): by variance (parameters above the type's and a
    result below, through `int` below `rational` and class subtyping), or a
    generic function at an instance, a comparable type parameter at a type
    built from the primitive comparable types; with at most the type's
    effects. -/
def fnFits (env : TyEnv) (s : Sig) (t : Ty) : Bool :=
  match t with
  | .struct m ts =>
    match FnValues.parseName m with
    | some (k, effs) =>
      -- (the effects only: a tuple parameter may be flattened, #231)
      let sh : FnValues.Shape := ⟨k, s.decides, s.suspends, s.fx⟩
      let qs0 := ts.take k
      let u := (ts.drop k).headD .void
      let subAt (a b : Ty) : Bool := a == b || (a == .int && b == .rational) || match a, b with
        | .struct x [], .struct y [] => x != y && env.isSub x y
        | _, _ => false
      -- (#231) the parameters as the type wants them: as they are, a single
      -- tuple parameter unflattened into the type's, or the parameters
      -- flattened into the type's single tuple parameter
      let reshaped : Option (List Ty × List Ty) :=
        if k == s.params.length then some (s.params, qs0)
        else match s.params, qs0 with
          | [.tup es], _ => if es.length == k then some (es, qs0) else none
          | _, [.tup es] => if es.length == s.params.length then some (s.params, es) else none
          -- (a single parameter, a type parameter say, at the tuple of the
          -- type's parameters: matching decides)
          | [_], _ => if k ≥ 2 then some (s.params, [.tup qs0]) else none
          | _, _ => none
      match reshaped with
      | none => false
      | some (ps, qs) =>
      sh.within (FnValues.shapeOf k effs) &&
        if s.tparams.isEmpty then
          (qs.zip ps).all (fun (q, p) => subAt q p) && subAt s.ret u
        else
          match ((ps ++ [s.ret]).zip (qs ++ [u])).foldlM (fun σ (a, b) => a.matchArg env σ b) [] with
          | some σ => s.tparams.all fun (v, cmp) => match σ.lookup v with
            | some x => !cmp || x.plainComparable
            | none => false
          | none => false
    | none => false
  | _ => false

/-- A generic value's instance at its own parameter/result shape. Unlike
    closed specialization, the expected type may mention the caller's
    parameters. `fixed` pins a bound method's receiver arguments. Bounds
    are checked here before constructing its value class. -/
def fnValueArgs (env : TyEnv) (s : Sig) (t : Ty) (fixed : List (String × Ty) := []) : Option (List Ty) := do
  let .struct m ts := t | none
  let some (k, es) := FnValues.parseName m | none
  if k != s.params.length || ts.length != k + 1 then none else do
    let own : FnValues.Shape := ⟨k, s.decides, s.suspends, s.fx⟩
    if !own.within (FnValues.shapeOf k es) then none else do
      let σ ← ((s.params ++ [s.ret]).zip ts).foldlM (fun σ (a, b) => a.matchArg env σ b) fixed
      if !((s.params ++ [s.ret]).zip ts).all (fun (a, b) => (a.subst σ).eqv b) then none else
      s.tparams.mapM fun (v, cmp) => do
        let t ← σ.lookup v
        if cmp && !t.comparable env then none else some t

/-- A symbolic adapter's parameters come from its own first function shape,
    including tuple adaptation. The original function signature stays intact. -/
def fnClassArgs (env : TyEnv) (cls : String) (target : Ty)
    (fixed : List (String × Ty) := []) : Option (List Ty) := do
  if !env.classes.contains cls then none else do
    let iface ← (env.info cls).ifaces.head?
    let (k, es) ← FnValues.parseName iface
    let ts := (env.iargs.lookup (cls, iface)).getD []
    let sig : Sig := {
      idx := 0, name := cls, params := ts.take k, ret := (ts.drop k).headD .void,
      decides := es.contains "decides", isConst := false,
      tparams := (env.sparams.lookup cls).getD [], fx := allowedFx es, suspends := es.contains "suspends" }
    fnValueArgs env sig target fixed

/-- A construction instance found with its original expected context. -/
structure ConstructHint where
  pos : Pos
  name : String
  site : String
  frame : String
  origin : String
  defaults : List (String × String)
  selfClass : Option String
  tag : String
  inputs : List (String × Ty)
  aliases : List (String × Ty)
  ty : Ty

structure Ctx where
  /-- How many retries without an expected type enclose this point: a later
      branch is elaborated against the first's type, else on its own (to
      join), at most a few levels deep (so nested ones stay linear). -/
  retries : Nat := 0
  constructProbe : Bool := false
  inlineScopes : List String := []
  constructOrigin : Option String := none
  constructHints : Option (List ConstructHint) := none
  sigs    : List Sig
  /-- The functions' `<decides>` flags, as a program, for `Expr.mayFail`. -/
  sigProg : Prog
  locals  : List Local := []
  frameName : String := ""
  frameArgs : List Ty := []
  canFail : Bool := false
  inLoop  : Bool := false
  /-- In a named parameter's default, elaborated at a call: no `return`. -/
  inParamDefault : Bool := false
  /-- The `defer:` bodies of the function's enclosing scopes, innermost first
      (#80): a `return` runs them all, a `break` those registered inside its
      loop (all but the first `loopDefers`). -/
  defers  : List (SExpr × List Local) := []
  loopDefers : Nat := 0
  /-- In a `defer:` body, which cannot `return`. -/
  inDefer : Bool := false
  /-- In a class's `block:` clauses (one method, `$block`), where a `return`
      would skip the clauses after it. -/
  inBlock : Bool := false
  retTy   : Ty := .void
  refineExits : Refine.Exits := {}
  types   : TyEnv := {}
  /-- The field defaults being elaborated (struct, field), to reject a default
      that depends on itself. -/
  defaults : List (String × String) := []
  /-- In a generic function, the slot of the hidden parameter that holds a
      value of its first type parameter (the others follow), and the names of
      its type parameters, in order. A field default is elaborated with its
      struct's type parameters in `types.tvars`, but its hidden arguments
      still come from the enclosing function's. -/
  dictBase : Nat := 0
  dictVars : List String := []
  /-- In the call of a dispatch's branch that opens type arguments (#209):
      each type parameter of the enclosing function that the refinement
      binds, as the type it binds it to and itself. The locals are typed
      under the refinement there, so a generic call infers its type
      arguments in terms of the opened ones, which have no values; its
      hidden arguments are built in terms of the function's own instead,
      whose values `Typed.dispatch` types under the refinement too. -/
  unrefine : List (Ty × Ty) := []
  /-- In a method of class `c` (the function `c.M`): `c`. A bare name that is
      not a local is then looked up among the fields and methods of `Self`.
      In a class's copy of an interface's default, the interface (#53). -/
  selfClass : Option String := none
  /-- In a class's copy of an interface's default (#53), and in the branches
      lifted from it: `$in` and the class, which tells its refining casts'
      lifts (#243) from those of the interface's own default and of the
      other classes' copies, at the same place in the source but at other
      types. -/
  liftTag : String := ""
  /-- A moved continuation's casts have fresh capture/storage metadata,
      independently of the class-copy tag and continuation sharing keys. -/
  refineScope : String := ""
  /-- In a method `c.M` (or `c.(r:)M`): `M` (or `(r:)M`), for `(super:)`. -/
  selfMethod : Option String := none
  /-- In a constructor's items (the function `K$init`, #72): no `return`. -/
  inCtor : Bool := false
  /-- In a `<suspends>` function (#156): calls of suspends functions allowed. -/
  suspends : Bool := false
  /-- In an arm of `sync`, `race` or `rush` (#156): a `return` returns from
      the function, cancelling the other arms. -/
  inArm : Bool := false
  /-- In a `branch` body (#156): no `return` (the Book's rule). -/
  inBranch : Bool := false
  /-- Checking a field's default once, as a failure context: the default is
      elaborated again at each construction that omits the field, in that
      construction's context (#156). -/
  inDefaultCheck : Bool := false
  /-- In the body of a `loop` or `for`, also through arms (#156): a
      `branch` there would start again before the last one ended. -/
  inRepeat : Bool := false
  /-- In the clauses of an `if` condition or `first{…}` that bind a choice
      (#208), inside a `loop`: a `break` there would leave the loop they are
      compiled to, not that one. -/
  inChoice : Bool := false
  /-- In the clauses of a failure context that takes a choice's values
      (#208): a choice that reaches the elaborator here is in a place it
      cannot be lifted from. -/
  inTaking : Bool := false
  /-- The internal loop that propagates a failed continuation outcome. -/
  forOutcomeSlot : Option Nat := none
  /-- A source-loop break crossing the internal loops of lazy producers. -/
  forBreakSlot : Option Nat := none
  /-- A source break carried by a shared for continuation. -/
  forBreakCapture : Option String := none
  /-- A source return carried by a shared for continuation. -/
  forReturnSlot : Option String := none
  forExitPacket : Option SExpr := none
  forStage : Option Choice.ForStagePlan := none
  forStageArgs : List Ty := []
  forStageFlat : Bool := false
  forStageCopies : List String := []
  forStageBorrows : List String := []
  resumeStorage : List (String × SourceStorage) := []
  /-- Inside a block or construction kept with a choice in it (`$noLift`,
      #283): what it is, for the message. -/
  liftWhy : String := ""
  /-- The effects the function being elaborated allows (#335): a
      continuation's, which runs only where that code would. -/
  fnFx : List String := []
  /-- Elaborating only for a type, apart (an `if`'s join, #331): no function
      of its own an earlier elaboration asked for (#275, #335), which is
      keyed by place and may take clauses that bind other names. -/
  typeOnly : Bool := false
  /-- Isolated mutual-generator inference: return this call's inferred type
      arguments after normal binding, without requiring witnesses. -/
  callInstanceProbe : Option String := none
  /-- (#283) Elaborating the call as written of an `$inlineOv(F, id, …)`,
      for types: the overload of `F` it takes is noted under `id`. -/
  ovPick : Option (Nat × String) := none
  /-- (#243, #351) Elaborating an `if` as written, whose condition has a
      cast as a later clause: not rewritten, `elabE`'s `.ite`. -/
  asWritten : Bool := false

/-- Compiler-owned inferred functions must see a registered helper's
    effects before their own signature can reach its fixed point. -/
def Ctx.infersHeapFx (ctx : Ctx) : Bool :=
  ctx.frameName.endsWith ".$block" || defaultBridge ctx.frameName ||
    ctx.types.castRequests.any (·.name == ctx.frameName)

/-- A generated frame does not make an immediate source operation suspend. -/
def Ctx.sourceSuspends (ctx : Ctx) (f : Nat) : Bool :=
  ctx.sigs.any fun s => s.idx == f && s.suspends &&
    if s.name.startsWith "$refine" then
      ((ctx.types.castRequests.find? (·.name == s.name)).map (·.sourceSuspends)).getD true
    else if s.name.startsWith "$forStage" && s.name.endsWith "$resume" then
      ((ctx.types.loopRequests.findSome? fun l =>
        l.stagePlan.filter (fun p => s.name.endsWith ("." ++ p.method))).map (·.sourceSuspends)).getD true
    else true

def Ctx.sourceWaits (ctx : Ctx) (e : Expr) : Bool :=
  Suspend.countSusp ctx.sourceSuspends (fun _ => false) false
    (fun f => ctx.sigs.any fun s => s.idx == f && (s.name == "$spawnMark" || s.name == "$branchMark")) e > 0

def Ctx.acceptsHelper (ctx : Ctx) (lift : Choice.FirstLift) : Bool :=
  ctx.infersHeapFx ||
    (lift.specs.filter (["reads", "writes", "allocates"].contains ·)).all ctx.fnFx.contains

/-- A lazily taken call where the first success is taken (#246): its
    function, where, the code it runs once for all the values of an item,
    where an argument of a call of itself sets a name, and the function of
    its own it is compiled as when that code has effects, or why it cannot
    be. -/
structure LoopUse where
  g : String
  pos : Pos
  itemCode : Expr
  argSet : Option Pos
  lift : Except String Choice.FirstLift

structure ESt where
  /-- Pure mutual groups whose changing instances need eager generation. -/
  eagerNeeds : List String := []
  /-- The program's types, for conversions between class types (`coerce`). -/
  env : TyEnv := {}
  nslots : Nat := 0
  /-- The type of each slot allocated so far (the certificate for `Prog.checkTypes`). -/
  slotTys : Array Ty := #[]
  /-- The heap effects of the function so far (#35): `allocates`, `reads`,
      `writes`, each with where it first occurs and the function called
      there, if it comes from a call. -/
  fx : List (String × Pos × Option String) := []
  /-- The type of each argument of an overloaded call elaborated alone, by
      its position and text (#74): computed once, so nested overloaded calls
      take polynomial time (it survives the trials' state being restored). -/
  natTys : Std.HashMap String (Option Ty) := {}
  /-- Successful receiver-class probes, keyed by syntax and lexical typing
      context. Shared by isolated trials so nested callbacks stay polynomial. -/
  methodReceivers : Std.HashMap String (Option String) := {}
  /-- Functions wanted as values at closed function types no class of
      theirs gives (#214). -/
  fnNeeds : List (String × Ty) := []
  methodNeeds : List FnValues.MethodRequest := []
  /-- Where the function calls `Err()` first, if it does: a function whose
      values are all computed at a call (#235) may reach none. -/
  errAt : Option Pos := none
  /-- Branches of casts that refine type arguments, to lift into functions
      (#243): the program is elaborated again, with them. -/
  castNeeds : List Refine.Lift := []
  /-- Encounters with suspending casts whose lift is still being discovered.
      Their placeholder expressions have no suspension to scan. -/
  pendingSuspendingCasts : Nat := 0
  /-- Pending casts that can wait on either path, for shared-slot checks. -/
  pendingWaitingCasts : Nat := 0
  /-- Source suspension hidden by provisional generated functions. -/
  pendingSourceSuspends : Nat := 0
  forStageUses : Nat := 0
  /-- Mutable locals captured by a branch or a potentially continuing rush arm. -/
  backgroundSlots : List Nat := []
  frameSlots : List (Nat × SourceStorage) := []
  frameCopies : List FrameRefs.CopyOut := []
  /-- The recursive functions with several values that a context taking
      its first success consumes lazily (#246), with where, and the code
      each runs once for all the values of an item (`LoopGen.itemCode`):
      it may reach no `Print` and change no object, checked on Verse Core
      code once every function is. -/
  loopFirst : List LoopUse := []
  /-- (#283) For a call of an overloaded function with several values: the
      overload the elaboration for types chose, by the call's `$inlineOv` id. -/
  ovPicks : List (Nat × String) := []
  constructHints : List ConstructHint := []
  deriving Inhabited

abbrev EM := StateT ESt (Except String)

/-- Successful isolated branch typing contributes construction instances
    during the construction probe, while its runtime slots/effects are reset. -/
def restoreConstructProbe (ctx : Ctx) (saved : ESt) : EM Unit := do
  let hints := (← get).constructHints
  let receivers := (← get).methodReceivers
  let restored := if ctx.constructProbe then { saved with constructHints := hints } else saved
  set { restored with methodReceivers := receivers }

/-- A call of a recursive function with several values that its consumer
    takes lazily (#246), as code for the consumer to put in its loop: the
    stack of items to run, a step that runs one of them, the slot that says
    whether that came to a value, and the value, which the consumer
    computes in its own failure context, so that what it does is undone
    with it, as for a choice's alternative. -/
structure LoopGen where
  /-- The stack with the call's item (its parameters are bound before). -/
  init : Expr
  /-- Pops an item and runs one alternative of it (its clauses first when
      it starts): a call of the function pushes an item, a value sets `has`. -/
  step : Expr
  /-- The slot of the stack's size: no items, no values left. -/
  sp : Nat
  has : Nat
  /-- The value the step came to, at `vty`, the function's result type:
      it may fail. -/
  value : Expr
  /-- What runs once the consumer took that value or rejected it: the item
      that resumes at the next alternative, if any, pushed with the names
      as the consumer left them (as a value's `set` of one is kept with it,
      or undone). -/
  after : Expr
  vty : Ty
  /-- The code that runs once for all the values of an item: its clauses,
      its conditions, the arguments of its calls of the function. -/
  itemCode : Expr
  /-- Where an argument of a call of the function by itself has a `set`:
      a context that takes its first success would not undo it with the
      values of that call it rejects. -/
  argSet : Option Pos

  /-- Each mutual member's signature parameters at this invocation. -/
  instances : List (String × List (String × Ty)) := []

/-- Run `m`, attributing the heap effects it records first to `p` (a field
    or argument default: the effect is the construction's or the call's). -/
def fxAt (p : Pos) (m : EM α) : EM α := do
  let before := (← get).fx.length
  let r ← m
  modify fun st => { st with fx := st.fx.take before ++ (st.fx.drop before).map fun (k, _, v) => (k, p, v) }
  return r

/-- Record heap effects at `p` (of a call of `via`). -/
def noteFx (p : Pos) (ks : List String) (via : Option String := none) : EM Unit :=
  modify fun st => { st with fx := ks.foldl (fun acc k =>
    if acc.any (·.1 == k) then acc else acc ++ [(k, p, via)]) st.fx }

/-- Record the outer mutable slots a task can still access after it starts. -/
def noteBackgroundCaptures (ctx : Ctx) (uses : List Nat) : EM Unit := do
  let slots := ctx.locals.filterMap fun l =>
    if l.mutable && uses.contains l.slot then some l.slot else none
  unless slots.isEmpty do
    modify fun st => { st with backgroundSlots := (slots ++ st.backgroundSlots).eraseDups }

/-- An elaborated expression and its type. -/
structure R where
  e  : Expr
  ty : Ty


/-- A new slot of the current frame, holding values of type `t`. -/
def fresh (t : Ty) : EM Nat :=
  modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push t })

def eerr (p : Pos) (msg : String) : EM α := throw s!"{p.show}: {msg}"

/-- A class's fields cannot be set: they are immutable until `var` fields,
    which need reference semantics, are supported. Setting one would make
    the tuple representation observable. -/
def classSetMsg (c f : String) : String :=
  s!"field '{f}' of class {c} is not a var: declare it with var {f}:t = …"

/-- Why values of type `t` cannot be used where equality is needed. -/
def notComparable (env : TyEnv) (t : Ty) (what : String) : String :=
  match t with
  | .struct n _ =>
    if (FnValues.parseName n).isSome then
      s!"{what} must be comparable, and {t.show} is a function type (Book of Verse ch. 4: functions are not comparable)"
    else if env.classes.contains n then
      s!"{what} must be comparable, and {t.show} is a class (only <unique> classes are comparable, by identity)"
    else notComparable.params t what
  | _ => notComparable.params t what
where
  params (t : Ty) (what : String) : String :=
  match t.params with
  | v :: _ => s!"{what} must be comparable, and {t.show} is not: declare {v}:subtype(comparable)"
  | [] => s!"{what} must be comparable, and {t.show} is not"

/-- A method's name as written: `M` for an overload `M$ovN` (#106). -/
def methodBase (x : String) : String := (x.splitOn "$ov").headD x

def builtins : List String :=
  ["Print", "ToString", "Floor", "Ceil", "Abs", "Min", "Max", "Quotient", "Mod", "Err", "ConcatenateMaps"]

/-- Built-in functions a program may also define (#127, #132): its own
    definition, if any, is the one a call means. -/
def softBuiltins : List String :=
  ["Round", "Int", "Sqrt", "Exp", "Ln", "Log", "Pow", "Sin", "Cos", "Tan", "ArcSin", "ArcCos", "ArcTan",
   "IsFinite", "Concatenate", "Sinh", "Cosh", "Tanh", "ArSinh", "ArCosh", "ArTanh", "Lerp"]

partial def resolveTy (env : TyEnv) (p : Pos) : STy → EM Ty
  | .name "int" => pure .int
  | .name "logic" => pure .logic
  | .name "char" => pure .char
  | .name "char32" => pure .char32
  | .name "rational" => pure .rational
  | .name "string" => pure Ty.string
  | .name "void" => pure .void
  | .name "float" => pure .float
  | .name "any" => pure .any
  | .name "$never" => pure .never
  | .name n =>
    if let some t := env.tvars.lookup n then pure t
    else if (env.structs.lookup n).isSome then
      match env.sparams.lookup n with
      | some ps => eerr p s!"{n} is parametric: write {n}(…) with {ps.length} type argument(s)"
      | none => pure (.struct n [])
    else if (env.enums.lookup n).isSome then pure (.enum n)
    else if (env.refines.lookup n).isSome then pure (.refine n)
    -- (an inlined generic call's type parameter, `$tp…_t`, that no
    -- argument determined, #283: said with its own name)
    else if n.startsWith "$tp" then
      eerr p s!"cannot infer type parameter {((n.dropWhile (· != '_')).drop 1).toString} of this call of a function with several values from its arguments"
    else eerr p s!"unknown type '{n}' (supported: int, logic, char, string, void, []t, ?t, tuple(…), and structs and enums)"
  | .arr t => return .arr (← resolveTy env p t)
  | .opt t => return .opt (← resolveTy env p t)
  | .tup [] => pure .void
  | .tup ts => return .tup (← ts.mapM (resolveTy env p))
  -- a function type: its shape's interface (#210)
  | .fn ps es r => do
    if es.contains "decides" && es.contains "suspends" then
      eerr p "a function type cannot be both <suspends> and <decides>, which exclude each other"
    resolveTy env p (.app (FnValues.shapeOf ps.length es).name (ps ++ [r]))
  | .map k v => do
    let kt ← resolveTy env p k
    if !kt.comparable env then eerr p (notComparable env kt "a map key")
    return .map kt (← resolveTy env p v)
  | .app "$methodResult" [.name receiver] => do
    let some t := env.tvars.lookup receiver | eerr p "internal: missing static method result"
    return t
  | .app n args => do
    let ts ← args.mapM (resolveTy env p)
    -- (#220: its handlers take the value, so an event without one has none)
    if n == "subscribable_event" && ts == [.void] && env.classes.contains "$subscription" then
      eerr p "subscribable_event(void) is not supported: an event without a value is subscribable_event(), whose functions take none (#220)"
    match env.sparams.lookup n with
    | some ps =>
      if ps.length != ts.length then eerr p s!"{n} takes {ps.length} type argument(s), found {ts.length}"
      for ((v, c), t) in ps.zip ts do
        if c && !t.comparable env then eerr p (notComparable env t s!"type argument {v} of {n}")
      let t := Ty.struct n ts
      if t.sizeUpTo env (maxTySize + 1) > maxTySize then
        eerr p s!"the type {n}(…) is too large: its Verse Core representation has more than {maxTySize} nodes"
      return t
    | none =>
      if (env.structs.lookup n).isSome then eerr p s!"struct {n} takes no type arguments"
      else eerr p s!"unknown parametric type '{n}' (only structs can be parametric)"

def Ctx.lookup (ctx : Ctx) (n : String) : Option Local := ctx.locals.find? (·.name == n)
def Ctx.sig? (ctx : Ctx) (n : String) : Option Sig := ctx.sigs.find? (·.name == n)

/-- Class or interface `c` has method `m`, its own or inherited. -/
def Ctx.hasMethod (ctx : Ctx) (c m : String) : Bool :=
  (ctx.types.supers c).any fun e => (ctx.sig? s!"{e}.{m}").isSome

/-- Arguments whose instance comes from the other arguments' types. A
    local or member shadows a same-named generic top-level function. -/
def Ctx.argNeedsType (ctx : Ctx) : SExpr → Bool
  | .ident _ "false" | .arrayLit _ [] | .mapLit _ [] => true
  | .ident _ n =>
    (ctx.lookup n).isNone &&
      !(ctx.selfClass.any fun c => (ctx.types.fields c).any (·.1 == n) || ctx.hasMethod c n ||
        ((ctx.types.methodOverloads.lookup n).map (·.any (ctx.hasMethod c ·))).getD false) &&
      (ctx.sig? n).any (fun f => !f.isConst && !f.tparams.isEmpty) &&
      ctx.types.classes.contains s!"{n}$fn"
  | _ => false

/-- Where the method `m` of `c` is declared, for the signature of a call: the
    most specific of the declarations at or above `c` and, among several,
    one whose result is below the others' (overrides may narrow it). -/
def Ctx.methodDecl? (ctx : Ctx) (c m : String) : Option String :=
  let env := ctx.types
  let cands := (env.supers c).filter fun e => (ctx.sig? s!"{e}.{m}").isSome
  let best := cands.filter fun e => !cands.any fun e' => e' != e && env.isSub e' e
  let retOf (e : String) : Ty := ((ctx.sig? s!"{e}.{m}").map (·.ret)).getD .void
  let below (a b : Ty) : Bool := a == b || match a, b with
    | .struct S [], .struct T [] => env.isSub S T
    | _, _ => false
  match best.find? (fun e => best.all fun e' => below (retOf e) (retOf e')) with
  | some e => some e
  | none => best.head?

/-- A method-local instance needs an expected function type. Fields and
    ambiguous overloads keep their ordinary lookup and diagnostics. -/
def Ctx.methodValueNeedsType (ctx : Ctx) (c m : String) : Bool :=
  if (ctx.types.fields c).any (·.1 == m) then false else
  let visible := if ctx.hasMethod c m then [m] else
    ((ctx.types.methodOverloads.lookup m).getD []).filter (ctx.hasMethod c ·)
  match visible with
  | [m] => match ctx.methodDecl? c m with
    | some owner => (ctx.sig? s!"{owner}.{m}").any fun s => s.named.isEmpty &&
        s.tparams.length > ((ctx.types.sparams.lookup owner).getD []).length
    | none => false
  | _ => false

/-- Classify a bound value using an isolated receiver type probe. Its code,
    slots, effects and helper requests never enter the actual call. -/
def argNeedsTypeWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (a : SExpr) : EM Bool := do
  if ctx.argNeedsType a then return true
  match a with
  | .ident _ n =>
    return (ctx.lookup n).isNone && ctx.selfClass.any (ctx.methodValueNeedsType · n)
  | .member _ receiver m =>
    -- Unreferenced dispatch temporaries have fresh names in each trial;
    -- they must not prevent sharing the same receiver's type lookup.
    let locals := ctx.locals.filter fun l => l.name == "Self" || l.name == "$Self" ||
      Choice.anyE (fun | .ident _ n => n == l.name | _ => false) receiver
    let key := reprStr (receiver, locals.map (fun l => (l.name, l.ty)), ctx.types.tvars,
      ctx.selfClass, ctx.selfMethod, ctx.fnFx, ctx.retTy, ctx.frameName, ctx.frameArgs, ctx.retries,
      [ctx.canFail, ctx.inTaking, ctx.suspends, ctx.inLoop, ctx.inParamDefault, ctx.inDefer,
       ctx.inBlock, ctx.inCtor, ctx.inArm, ctx.inBranch, ctx.inDefaultCheck, ctx.inRepeat,
       ctx.inChoice, ctx.asWritten, ctx.constructProbe], ctx.defaults, ctx.inlineScopes,
      ctx.constructOrigin, ctx.unrefine)
    let saved ← get
    if let some c := saved.methodReceivers[key]? then
      return c.any (ctx.methodValueNeedsType · m)
    match (elabE { ctx with typeOnly := true, callInstanceProbe := none } receiver none).run saved with
    | .ok (r, probed) =>
      let c := match r.ty with
        | .struct c _ => if ctx.types.classes.contains c then some c else none
        | _ => none
      modify fun st => { st with methodReceivers := probed.methodReceivers.insert key c }
      return c.any (ctx.methodValueNeedsType · m)
    | .error _ => return false
  | _ => return false

/-- How `e` implements slot `r` of method `m`: its `(r:)m`, else its plain
    `m` when not abstract. -/
def Ctx.implAt (ctx : Ctx) (r m e : String) : Option String :=
  if (ctx.sig? s!"{e}.({r}:){m}").isSome then some s!"{e}.({r}:){m}"
  else if (ctx.sig? s!"{e}.{m}").isSome && !ctx.types.abstracts.contains (e, m) then some s!"{e}.{m}"
  else none

/-- The slots of method `m` above `c` (`TyEnv.rootsOf`). -/
def Ctx.rootsOf (ctx : Ctx) (c m : String) : List String :=
  ctx.types.rootsOf (fun e => (ctx.sig? s!"{e}.{m}").isSome) c

/-- The function that implements slot `r` of method `m` for an instance of
    class `d` (#70). -/
def Ctx.implFor? (ctx : Ctx) (d r m : String) : Option String :=
  (ctx.types.slotImpls (ctx.implAt r m) (ctx.types.supers d) r).head?

def p2 (op : Prim) (a b : Expr) : Expr := .prim op [a, b]

/-- The slot of the hidden parameter for type parameter `n`. -/
def TyEnv.dictSlot? (env : TyEnv) (dictBase : Nat) (n : String) : Option Nat :=
  if env.dictOrder.isEmpty then (env.tvars.findIdx? (·.1 == n)).map (dictBase + ·)
  else (env.dictOrder.idxOf? n).map (dictBase + ·)

/-- A value of type `t`, built by an expression whose Verse Core type the
    checker infers exactly (`tc e none`): the hidden argument a call of a
    generic function passes for a type argument `t`. It is only ever used to
    initialise slots, so which value it is does not matter. A class
    reference is a fresh slot of exactly its type (`new` would infer only
    the class constructed), which starts as a placeholder. -/
partial def witness (env : TyEnv) (dictBase : Nat) (dictVars : List String) : Ty → EM Expr
  | .int | .char32 | .enum _ => pure (.lit (.int 0))
  | .rational => pure (.lit (.tup [.int 0, .int 1]))
  | .refine n => match env.refines.lookup n with
    | some (.float, _) => pure (.lit (.float 0))
    | _ => pure (.lit (.int 0))
  | .float => pure (.lit (.float 0))
  | .any => pure (.lit .void)
  | .logic => pure (.lit (.logic false))
  | .char => pure (.lit (.char 0))
  | .void | .never => pure (.lit .void)
  | .arr t => return .prim .mkArr [← witness env dictBase dictVars t]
  | .opt t => return .prim .mkSome [← witness env dictBase dictVars t]
  | .tup ts => return .prim .mkTup (← ts.mapM (witness env dictBase dictVars))
  | .map k v => return .prim .mkArr [.prim .mkTup [← witness env dictBase dictVars k, ← witness env dictBase dictVars v]]
  | .struct n ts => do
    if env.isRefClass n then return .local (← fresh (.struct n ts))
    if env.classes.contains n then
      -- every option set, so that the checker infers the type (the value is
      -- never observed)
      return .prim .mkTup (← (env.concreteBelow n).mapM fun d => do
        return .prim .mkSome [.prim .mkTup (← (env.fields d (if d == n then ts else [])).mapM fun (_, t, _) =>
          witness env dictBase dictVars t)])
    return .prim .mkTup (← (env.fields n ts).mapM fun (_, t, _) => witness env dictBase dictVars t)
  -- a type parameter of the enclosing function: its hidden parameter (an
  -- unknown one cannot occur; the checker would reject the program; a
  -- generic call at a type a dispatch opens is refused before, #209)
  | .param n _ => pure <| match dictVars.idxOf? n with
    | some j => .local (dictBase + j)
    | none => .lit .void

/-- Whether a Verse Core type mentions a type variable, also as a type
    argument of a reference type (a task's result, #204). -/
partial def _root_.OpenVerse.VTy.mentionsVar : VTy → Bool
  | .var _ => true
  | .arr t | .opt t => t.mentionsVar
  | .tup ts | .ref _ ts | .vref _ ts => ts.any VTy.mentionsVar
  | _ => false

/-- Whether a Verse Core type mentions a reference. -/
partial def _root_.OpenVerse.VTy.hasRef : VTy → Bool
  | .ref _ _ | .vref _ _ => true
  | .arr t | .opt t => t.hasRef
  | .tup ts => ts.any VTy.hasRef
  | _ => false

/-- The value a slot of type `t` starts with (`DefaultE`), in a function
    whose parameters (hidden ones included) have types `params`: the default
    literal of its Verse Core type (also when only `[]` or the empty option
    mentions a type variable or a reference), the hidden parameter of a type
    parameter, a parameter of a subtype, a placeholder object of the first
    concrete class below a class (#34), or a tuple of such. `visiting` are
    the class types (with their type arguments, #39) whose placeholders are
    being built. -/
partial def slotDefault (env : TyEnv) (dictBase : Nat) (params : List Ty) (visiting : List String)
    (t : Ty) : Except String Expr := do
  let vt := t.toVTy env
  if !vt.mentionsVar && !vt.hasRef then return .lit vt.default
  -- a parameter of a subtype: no allocation
  if vt.hasRef then
    if let some i := params.findIdx? (fun pt => (pt.toVTy env).sub vt) then return .local i
  match t with
  | .param n _ =>
    if let some k := env.selfWitness.lookup n then return .heap (.get k) [.local 0]
    match env.dictSlot? dictBase n with
    | some d => return .local d
    | none => return .lit vt.default
  | .tup ts => return .prim .mkTup (← ts.mapM (slotDefault env dictBase params visiting))
  | .struct n ts =>
    -- a prototype of a class below `n` (#37): no allocation
    if env.isRefClass n then
      -- (the classes below and the type arguments once, not per prototype:
      -- a dispatch over n classes makes n such slots)
      let below := env.concreteBelow n
      let args := env.coreArgs n ts
      if let some (_, a) := env.protos.zipIdx.find? fun (x : (String × Nat × List Value) × Nat) =>
          below.contains x.1.1 && (if env.viewed.contains n then env.viewOf n x.1.1 (env.coreArgs x.1.1 [])
            else env.coreArgs x.1.1 []) == args then
        return .lit (.ref a)
    if env.isRefClass n then
      -- the first class below `n` whose placeholder needs no instance of a
      -- class whose placeholder is being built
      let selfErr := s!"no class at or below {n} can be constructed without an instance of itself, so a variable or temporary of type {(Ty.struct n ts).show} has no initial value"
      let mut lastErr := selfErr
      -- (a failure for want of an instance of itself deeper down is this
      -- one, at the type the slot has: other failures are passed on)
      let keep (msg : String) : String := if msg.startsWith "no class at or below " then selfErr else msg
      -- (instantiations that grow without end are cut off: a large one
      -- inside a smaller one, not a large one by itself, which a class
      -- below at deeply nested type arguments is)
      let key := (Ty.struct n ts).show
      if visiting.length > 16 || (key.length > 400 && visiting.any (·.length < key.length)) then throw lastErr
      let args := (env.coreArgs n ts).map (Ty.toVTy env)
      let mut pinnedOut : List String := []
      for d in env.concreteBelow n do
        let dkey := s!"{d} as {key}"
        if visiting.contains dkey then continue
        -- (an object agrees with its class's pins, #142; through a view,
        -- at the type arguments that give the slot's, #351)
        let viewArgs := if env.viewed.contains n then env.viewArgs? n d (env.coreArgs n ts) else none
        if env.viewed.contains n then
          if viewArgs.isNone then
            pinnedOut := pinnedOut ++ [d]
            continue
        else if !VTy.pinsOK (env.lowerPins (env.corePins d)) args then
          pinnedOut := pinnedOut ++ [d]
          continue
        -- (its fields at the slot's type arguments, #39)
        let seen := match viewArgs with
          | some dargs => env.fieldsSeen d dargs d
          | none => env.fieldsSeen n ts d
        match seen.mapM fun (_, ft, _) =>
            slotDefault env dictBase params (dkey :: visiting) ft with
        | .ok fs => return .heap (.new (env.tagOf d)) fs
        | .error msg => lastErr := keep msg
      -- (no class can be built: one that some pins ruled out, or that
      -- needs more type arguments than the slot's, #209)
      if !pinnedOut.isEmpty then
        -- (its hidden placeholder class, or another's below it, which fix
        -- no more than it does, #157)
        let h0 := s!"{n}$placeholder"
        let hs := (if env.phs.contains h0 then [h0] else []) ++ env.phs.filter fun h => h != h0 && env.isSub h n
        for h in hs do
          -- (again only at a part of each type it is being built at: a
          -- placeholder at others is another object, `slot(slot(u))`'s
          -- holds `slot(u)`'s, and the types shrink, so this ends; one at
          -- types that grow, `n(t)`'s holding `n([]t)`'s, never would)
          let hpre := s!"{h} as "
          let hkey := hpre ++ key
          let shrinks := visiting.all fun v =>
            !v.startsWith hpre ||
              (let k0 := String.ofList (v.toList.drop hpre.length)
               key.length < k0.length && (k0.splitOn key).length > 1)
          if shrinks then
            match (env.fieldsSeen n ts h).mapM fun (_, ft, _) => slotDefault env dictBase params (hkey :: visiting) ft with
            | .ok fs => return .heap (.new (env.tagOf h)) fs
            | .error msg => lastErr := keep msg
        if !hs.isEmpty then throw lastErr
        throw s!"a variable or temporary of type {key} needs an initial value, and every class below {n} ({", ".intercalate pinnedOut}) fixes type arguments that {key} does not have, so none can be it (#142)"
      throw lastErr
    -- a parametric class starts with no option set, which has every such type
    if env.classes.contains n then return .lit vt.default
    return .prim .mkTup (← (env.fields n ts).mapM fun (_, t, _) => slotDefault env dictBase params visiting t)
  -- `[]`, the empty option and an empty map have every such type
  | _ => return .lit vt.default

/-- An instance of class `d` (its fields `rep`) as a value of static type
    `T` above it: `rep` in `d`'s option, the others empty. -/
def classWrap (env : TyEnv) (T d : String) (rep : Expr) : Expr :=
  .prim .mkTup ((env.concreteBelow T).map fun e => if e == d then .prim .mkSome [rep] else .lit .none)

/-- The value of a literal expression: a number, or a negated one. -/
def litValue? : Expr → Option Value
  | .lit (.int n) => some (.int n)
  | .lit (.float b) => some (.float b)
  | .prim .neg [.lit (.int n)] => some (.int (-n))
  | .prim .fneg [.lit (.float b)] => some (.float (VFloat.canon (-(VFloat.ofBits b))))
  | _ => none

/-- `a x` or `an x`. -/
def withArticle (x : String) : String :=
  if ["a", "e", "i", "o", "u"].any (x.startsWith ·) then s!"an {x}" else s!"a {x}"

def showLit (e : Expr) : String :=
  match litValue? e with
  | some v => v.render
  | none => "the value"

/-- `v` meets the conditions `_X op bound` of a refinement (#136). -/
def refineHolds (conds : List (String × Value)) (v : Value) : Bool :=
  conds.all fun (op, bound) =>
    match v, bound with
    | .int x, .int y => match op with
      | "<" => x < y | "<=" => x ≤ y | ">" => x > y | _ => x ≥ y
    | .float x, .float y =>
      let (fx, fy) := (VFloat.ofBits x, VFloat.ofBits y)
      match op with
      | "<" => fx < fy | "<=" => fx ≤ fy | ">" => fy < fx | _ => fy ≤ fx
    | _, _ => false

/-- A literal where a refinement is expected (#136): of that refinement
    when it meets its conditions (so that `if (C?) then 5 else 6`,
    `option{5}` and `(5, 1)` take it from their context). -/
def litAt (env : TyEnv) (exp : Option Ty) (r : R) : R :=
  match exp with
  | some (.refine n) =>
    match env.refines.lookup n, litValue? r.e with
    | some (base, conds), some v => if base == r.ty && refineHolds conds v then ⟨r.e, .refine n⟩ else r
    | _, _ => r
  | _ => r

/-- `v < w` on numbers of one base. -/
def numLt : Value → Value → Bool
  | .int x, .int y => x < y
  | .float x, .float y => VFloat.ofBits x < VFloat.ofBits y
  | _, _ => false

def numNeg : Value → Value
  | .int x => .int (-x)
  | .float x => .float (VFloat.canon (-(VFloat.ofBits x)))
  | v => v

/-- A refinement's interval: its tightest lower and upper bounds, each with
    whether it is strict (#143). -/
def refineInterval (conds : List (String × Value)) : Option (Value × Bool) × Option (Value × Bool) :=
  conds.foldl (fun (lo, hi) (op0, b0) =>
    -- (an int's strict bound is the next one, not strict: `< 10` is `<= 9`)
    let (op, b) : String × Value := match op0, b0 with
      | "<", .int x => ("<=", .int (x - 1))
      | ">", .int x => (">=", .int (x + 1))
      | o, v => (o, v)
    let strict := op == "<" || op == ">"
    if op == ">" || op == ">=" then
      let lo' := match lo with
        | none => some (b, strict)
        | some (l, ls) => if numLt l b || (l == b && strict && !ls) then some (b, strict) else some (l, ls)
      (lo', hi)
    else
      let hi' := match hi with
        | none => some (b, strict)
        | some (h, hs) => if numLt b h || (h == b && strict && !hs) then some (b, strict) else some (h, hs)
      (lo, hi')) (none, none)

/-- Interval `a` lies within `b`. -/
def intervalWithin (a b : Option (Value × Bool) × Option (Value × Bool)) : Bool :=
  let lowOk := match a.1, b.1 with
    | _, none => true
    | none, some _ => false
    | some (al, as), some (bl, bs) => numLt bl al || (al == bl && (as || !bs))
  let highOk := match a.2, b.2 with
    | _, none => true
    | none, some _ => false
    | some (ah, as), some (bh, bs) => numLt ah bh || (ah == bh && (as || !bs))
  lowOk && highOk

/-- The interval of `-X` for `X` in `i`. -/
def intervalNeg (i : Option (Value × Bool) × Option (Value × Bool)) : Option (Value × Bool) × Option (Value × Bool) :=
  (i.2.map fun (v, s) => (numNeg v, s), i.1.map fun (v, s) => (numNeg v, s))

/-- A refinement's value as its base (#136): operators, comparisons and
    ToString see the base type. -/
def widenR (env : TyEnv) (r : R) : R :=
  match r.ty with
  | .refine n => match env.refines.lookup n with
    | some (base, _) => ⟨r.e, base⟩
    | none => r
  | _ => r

/-- The conditions of `type{_X:base where c, …}` as `_X op bound`: each
    compares the variable with a literal number (Book of Verse ch. 11). -/
def refineConds (p : Pos) (v : String) (base : Ty) (conds : List SExpr) :
    Except String (List (String × Value)) := do
  if !(base == .int || base == .float) then
    throw s!"{p.show}: a refinement type refines an int or a float, not {base.show}"
  let intBound (n : Int) : Except String Value :=
    if Int64.inRange n then pure (.int n)
    else throw s!"{p.show}: the bound {n} does not fit in 64 bits"
  let bound : SExpr → Except String Value := fun
    | .int _ n => if base == .int then intBound n
      else throw s!"{p.show}: a float refinement's bound is a float literal (write {n}.0)"
    | .neg _ (.int _ n) => if base == .int then intBound (-n)
      else throw s!"{p.show}: a float refinement's bound is a float literal (write -{n}.0)"
    | .float _ b => if base == .float then pure (.float b)
      else throw s!"{p.show}: an int refinement's bound is an int literal"
    | .neg _ (.float _ b) => if base == .float then pure (.float (VFloat.canon (-(VFloat.ofBits b))))
      else throw s!"{p.show}: an int refinement's bound is an int literal"
    | .ident _ "Inf" => if base == .float then pure (.float 0x7FF0000000000000)
      else throw s!"{p.show}: an int refinement's bound is an int literal"
    | .neg _ (.ident _ "Inf") => if base == .float then pure (.float 0xFFF0000000000000)
      else throw s!"{p.show}: an int refinement's bound is an int literal"
    | .ident _ "NaN" => throw s!"{p.show}: NaN cannot bound a refinement"
    | _ => throw s!"{p.show}: a refinement's bound is a literal number, not a variable or an expression"
  let flip : String → String := fun | "<" => ">" | "<=" => ">=" | ">" => "<" | _ => "<="
  conds.mapM fun c => do
    match c with
    | .cmp _ a [(op, b)] =>
      if !["<", "<=", ">", ">="].contains op then
        throw s!"{p.show}: a refinement's condition is <, <=, > or >=, not {op}"
      match a, b with
      | .ident _ x, rhs => if x == v then return (op, ← bound rhs) else
          match rhs with
          | .ident _ y => if y == v then return (flip op, ← bound a) else
              throw s!"{p.show}: a refinement's condition compares {v} with a literal number"
          | _ => throw s!"{p.show}: a refinement's condition compares {v} with a literal number"
      | lhs, .ident _ y => if y == v then return (flip op, ← bound lhs) else
          throw s!"{p.show}: a refinement's condition compares {v} with a literal number"
      | _, _ => throw s!"{p.show}: a refinement's condition compares {v} with a literal number"
    | _ => throw s!"{p.show}: a refinement's condition is a comparison of {v} with a literal number"

/-- Convert a value `e` of type `a` to the supertype `b`, when `a` is a class
    below the class or interface `b`, or an array or option of such (arrays
    and options are covariant): the options of the classes below `a` move to
    their places among those below `b`. -/
partial def convert (env : TyEnv) (e : Expr) (a b : Ty) : EM (Option Expr) := do
  -- (a conversion's temporary or its element of type `false` holds no value:
  -- the code that made it left before, so `Err()` stands for it, of every
  -- type, not the `void` Verse Core has for its slot, #290)
  if a == .never && b != .never && b != .void then
    match e with
    | .local _ | .prim (.tupGet _) _ => return some (.prim .userErr [])
    | _ => pure ()
  -- references: the same value has both types (Verse Core subtyping, #32)
  if refUp env a b then return some e
  -- no value has a class type with no concrete class below it (an interface
  -- nothing implements, an abstract class with no subclass): the conversion
  -- to a type above it is unreachable (#98)
  if let (.struct S _, .struct T _) := (a, b) then
    if env.classes.contains S && env.classes.contains T && S != T && env.isSub S T &&
        (env.concreteBelow S).isEmpty then
      return some (.seq e (.prim .userErr []))
  match a, b with
  -- `int` is a subtype of `rational` (#116): `X` is `X / 1`
  | .int, .rational => return some (.prim .mkTup [e, .lit (.int 1)])
  -- every value is an `any`, evaluated (#138)
  | _, .any => return some (.seq e (.lit .void))
  -- a refinement is its base (#136); the base is the refinement only for a
  -- literal that meets its conditions (else a cast, `age[X]`)
  -- (a refinement within another's interval is one of it, #143)
  | .refine n, .refine m =>
    match env.refines.lookup n, env.refines.lookup m with
    | some (bn, cn), some (bm, cm) =>
      if bn == bm && intervalWithin (refineInterval cn) (refineInterval cm) then return some e else return none
    | _, _ => return none
  | .refine n, b =>
    match env.refines.lookup n with
    | some (base, _) => if base == b then return some e else convert env e base b
    | none => return none
  | a, .refine n =>
    match env.refines.lookup n, litValue? e with
    | some (base, conds), some v => if base == a && refineHolds conds v then return some e else return none
    | _, _ => return none
  | .struct S [], .struct T [] =>
    if env.classes.contains S && env.classes.contains T && S != T && env.isSub S T then
      let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a })
      let below := env.concreteBelow S
      let parts := (env.concreteBelow T).map fun d => match below.idxOf? d with
        | some j => Expr.prim (.tupGet j) [.local x]
        | none => .lit .none
      return some (.seq (.assign x e) (.prim .mkTup parts))
    else return none
  | .arr a', .arr b' =>
    let i ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a' })
    match ← convert env (.local i) a' b' with
    | some c => return some (.forE i e (.lit (.logic true)) c)
    | none => return none
  | .opt a', .opt b' =>
    let i ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a' })
    match ← convert env (.local i) a' b' with
    | some c =>
      -- (the option first, so that its code is not in the condition: it may
      -- suspend, #156)
      let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a })
      return some (.seq (.assign x e) (.ite (.assign i (.prim .query [.local x])) (.prim .mkSome [c]) (.lit .none)))
    | none => return none
  -- a map of convertible values is a map of the converted ones (#297)
  | .map k a', .map k' b' =>
    if k != k' then return none
    let i ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push (.tup [k, a']) })
    match ← convert env (.prim (.tupGet 1) [.local i]) a' b' with
    | some c => return some (.forE i e (.lit (.logic true)) (.prim .mkTup [.prim (.tupGet 0) [.local i], c]))
    | none => return none
  -- a tuple of convertible elements is a tuple of the converted ones
  | .tup ts, .tup us =>
    if ts.length != us.length then return none
    let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a })
    let mut es : Array Expr := #[]
    for ((ti, ui), i) in (ts.zip us).zip (List.range ts.length) do
      let ei := Expr.prim (.tupGet i) [.local x]
      -- (an element that never gives a value left the tuple before this
      -- runs: its place holds `Err()`, of every type, not the `void` its
      -- slot has, #290)
      if ti == .never && ui != .never then es := es.push (.prim .userErr [])
      else if ti == ui || ti == .never then es := es.push ei
      else match ← convert env ei ti ui with
        | some c => es := es.push c
        | none => return none
    return some (.seq (.assign x e) (.prim .mkTup es.toList))
  -- a tuple is an array of its elements (Book of Verse ch. 3), each at the
  -- element type
  | .tup ts, .arr t =>
    let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a })
    let mut es : Array Expr := #[]
    for (ti, i) in ts.zip (List.range ts.length) do
      let ei := Expr.prim (.tupGet i) [.local x]
      if ti == .never && t != .never then es := es.push (.prim .userErr [])
      else if ti == t || ti == .never then es := es.push ei
      else match ← convert env ei ti t with
        | some c => es := es.push c
        | none => return none
    return some (.seq (.assign x e) (.prim .mkArr es.toList))
  | _, _ => return none

/-- A tuple literal whose element of type `never` was followed by `void`,
    for a Verse Core that infers the tuple's type (#285), taken to a type
    that has another type there: the element as it was, which has every
    type (nested tuples too). -/
partial def unwrapNever : Expr → Ty → Ty → Expr
  | .prim .mkTup es, .tup ts, .tup us =>
    if es.length == ts.length && ts.length == us.length then
      .prim .mkTup ((es.zip (ts.zip us)).map fun (e, t, u) => match e, t with
        | .seq e' (.lit .void), .never => if u == .void || u == .never then e else e'
        | e, .tup _ => unwrapNever e t u
        | e, _ => e)
    else .prim .mkTup es
  | .prim .mkArr es, .arr .never, .arr u =>
    if u == .void || u == .never then .prim .mkArr es
    else .prim .mkArr (es.map fun e => match e with
      | .seq e' (.lit .void) => e'
      | e => e)
  | e, _, _ => e

/-- Convert `r` to type `target`: equal types, `false` (bottom) to anything,
    anything to `void` (Book of Verse: "void accepts any value"), and a
    class to a class or interface above it (`convert`). -/
def coerce (p : Pos) (r : R) (target : Ty) : EM Expr := do
  let r : R := { r with e := unwrapNever r.e r.ty target }
  -- (a value of type `false` read out of a temporary, a tuple, an array, an
  -- option or a field has `void` in Verse Core: it is evaluated, which may
  -- fail, and `Err()` follows, never reached, into a temporary of the target
  -- type, so that its type can be inferred anywhere, #297)
  -- (also after statements that compute its operands: a map's lookup)
  let rec projection : Expr → Bool
    | .local _ | .prim (.tupGet _) _ | .prim .index _ | .prim .query _ | .heap (.get _) _ => true
    | .seq _ b => projection b
    | _ => false
  if r.ty == .never && target != .never && target != .void && projection r.e then
    let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push target })
    return .assign x (.seq r.e (.prim .userErr []))
  if r.ty == target || r.ty == .never then return r.e
  if target == .void then return .seq r.e (.lit .void)
  match ← convert (← get).env r.e r.ty target with
  | some e =>
    -- a typed temporary: the checker cannot infer the type of an empty option
    let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push target })
    return .assign x e
  | none =>
    if let .refine n := target then
      if let some (base, _) := (← get).env.refines.lookup n then
        if r.ty == base then
          if (litValue? r.e).isSome then eerr p s!"{showLit r.e} is not {withArticle n}: it does not meet its conditions"
          eerr p s!"{withArticle base.show} is {withArticle n} only after a cast: write {n}[X], which fails when X is not one"
    eerr p s!"expected {target.show}, found {r.ty.show}"

/-- Build a variance adapter only when the ordinary parameter/result
    conversions succeed. Its private parameters preserve the caller's bounds
    without retaining caller names or borrowing its witness slots. -/
def methodVarianceRequest (ctx : Ctx) (p : Pos) (owner method : String)
    (receiver own target : Ty) : EM (Option (FnValues.MethodRequest × List Ty)) := do
  let .struct on ots := own | return none
  let .struct tn tts := target | return none
  let some (n, oe) := FnValues.parseName on | return none
  let some (k, te) := FnValues.parseName tn | return none
  if ots.length != n + 1 || tts.length != k + 1 ||
      !(FnValues.shapeOf k oe).within (FnValues.shapeOf k te) then return none
  -- Exact signatures and ordinary effect subtyping keep their existing
  -- adapter, including receiver bounds supplied by a GADT view.
  if n == k && ots == tts then return none
  let ps := ots.take n
  let qs := tts.take k
  let r := (ots.drop n).headD .void
  let u := (tts.drop k).headD .void
  let xs := (List.range k).map fun i => SExpr.ident p s!"$X{i}"
  let tuple? : Ty → Option (List Ty)
    | .void => some []
    | .tup ts => some ts
    | _ => none
  let mut choices : List (String × List Ty × List Ty × List SExpr) := []
  if n == k then choices := [("direct", ps, qs, xs)]
  if let [q] := qs then
    if let some es := tuple? q then
      if es.length == n then
        choices := choices ++ [("pack", ps, es, (List.range n).map fun i =>
          .app p (.ident p "$X0") [.int p (i : Int)] false)]
  if let [pt] := ps then
    if let some es := tuple? pt then
      if es.length == k then choices := choices ++ [("unpack", es, qs, [.tuple p xs])]
  if n == 1 && k != 1 then
    choices := choices ++ [("tuple", ps, [.tup qs], [.tuple p xs])]
  let saved ← get
  let fits (a b : Ty) : Bool :=
    match (do
      let slot ← fresh a
      discard <| coerce p ⟨.local slot, a⟩ b).run { saved with env := ctx.types } with
    | .ok _ => true
    | .error _ => false
  if !fits r u then return none
  for (kind, ps, qs, args) in choices do
    if !(qs.zip ps).all (fun (q, p) => fits q p) then continue
    let vars := Ty.mergeParamBounds (receiver.paramsC ++ target.paramsC)
    let names := vars.zipIdx.map fun ((n, _), i) => (n, STy.name s!"$methodVariance{i}")
    let st := fun t : Ty => t.toSTy.substNames names
    let receiver := st receiver
    let params := (tts.take k).map st
    let ret := st u
    let bounds := vars.map (·.2)
    let req : FnValues.MethodRequest := {
      key := reprStr (owner, method, receiver, params, te, ret, bounds, kind),
      pos := p, owner, method, receiver, params, effs := te, ret, args,
      decides := oe.contains "decides",
      tparams := vars.zipIdx.map fun ((_, cmp), i) => {
        pos := p, name := s!"$methodVariance{i}", constraint := if cmp then "comparable" else "type" } }
    return some (req, vars.map fun (n, cmp) => Ty.param n cmp)
  return none

/-- A type above both `a` and `b` (the expected one when it is, #32): two
    classes join at their nearest common supertype, and arrays, options,
    tuples and maps' values join covariantly. -/
partial def joinTy (env : TyEnv) (a b : Ty) (exp : Option Ty) (inner : Bool := false) : Option Ty :=
  if a == .never then some b
  else if b == .never then some a
  else if a == b then some (a.commonBounds b)
  else match a, b with
  | .int, .rational | .rational, .int => if inner then none else some .rational
  -- (refinements join at an expected refinement holding both, or at the
  -- wider of the two, #143)
  | .refine n, .refine m =>
    let within (x y : String) : Bool := match env.refines.lookup x, env.refines.lookup y with
      | some (bx, cx), some (by_, cy) => bx == by_ && intervalWithin (refineInterval cx) (refineInterval cy)
      | _, _ => false
    match exp with
    | some (.refine e) => if within n e && within m e then some (.refine e)
      else if within n m then some (.refine m) else if within m n then some (.refine n)
      else (env.refines.lookup n).map (·.1)
    | _ => if within n m then some (.refine m) else if within m n then some (.refine n)
      else match env.refines.lookup n, env.refines.lookup m with
        | some (bn, _), some (bm, _) => if bn == bm then some bn else none
        | _, _ => none
  | .refine n, b | b, .refine n =>
    match env.refines.lookup n, b with
    | some (base, _), .refine m => if (env.refines.lookup m).map (·.1) == some base then some base else none
    | some (base, _), b => if base == b then some base else none
    | none, _ => none
  | .struct S as, .struct T bs =>
    -- (inside a container, only references convert for free)
    if env.classes.contains S && env.classes.contains T &&
        (!inner || (env.isRefClass S && env.isRefClass T)) then
      -- the expected type, when both are below it, else the nearest common
      -- class above both, else the one interface above both that no other
      -- common one is below (at the same type arguments, #39)
      let up (U : String) (us : List Ty) : Bool :=
        env.isSub S U && env.isSub T U && env.upArgs S as U == us && env.upArgs T bs U == us
      let atU (U : String) : Ty :=
        (Ty.struct U (env.upArgs S as U)).commonBounds (.struct U (env.upArgs T bs U))
      let cands := (env.supers S).filter fun U => up U (env.upArgs S as U)
      let common : Option Ty :=
        match cands.find? fun U => !(env.info U).isIface with
        | some U => some (atU U)
        | none =>
          match cands.filter (fun U => !cands.any fun U' => U' != U && env.isSub U' U) with
          | [U] => some (atU U)
          | _ => none
      match exp with
      | some (.struct U us) => if env.classes.contains U && up U us then some (atU U) else common
      | _ => common
    else none
  | .arr x, .arr y => (joinTy env x y (match exp with | some (.arr e) => some e | _ => none) true).map .arr
  | .opt x, .opt y => (joinTy env x y (match exp with | some (.opt e) => some e | _ => none) true).map .opt
  -- (a tuple and an array join as an array, as do tuples of different
  -- lengths where an array is expected: a tuple converts to one)
  | .tup xs, .arr y | .arr y, .tup xs =>
    let e := match exp with | some (.arr e) => some e | _ => none
    (xs.foldlM (fun acc x => joinTy env acc x e true) y).map .arr
  | .tup xs, .tup ys =>
    if xs.length != ys.length then
      match exp with
      | some (.arr e) => ((xs ++ ys).foldlM (fun acc x => joinTy env acc x (some e) true) e).map .arr
      | _ => none
    else
      let es : List (Option Ty) := match exp with
        | some (.tup ets) => if ets.length == xs.length then ets.map some else xs.map fun _ => none
        | _ => xs.map fun _ => none
      ((xs.zip ys).zip es).mapM (fun ((x, y), e) => joinTy env x y e true) |>.map .tup
  | .map k x, .map k' y =>
    if k == k' then (joinTy env x y (match exp with | some (.map _ e) => some e | _ => none) true).map (.map k) else none
  | _, _ => none

/-- The type of a two-branch construct (`joinTy`; a void branch makes it void). -/
def join (p : Pos) (a b : Ty) (exp : Option Ty) : EM Ty := do
  match exp with
  | some .void => return .void
  | _ =>
    -- void accepts any value (Book of Verse), so a void branch makes the
    -- construct void: `if{X := e} else {Print("none")}`
    if a != .never && b != .never && !(a == b) && (a == .void || b == .void) then return .void
    match joinTy (← get).env a b exp with
    | some t => return t
    | none =>
      -- (types with nothing in common join at `any`, when nothing else is
      -- expected, #138; classes with two common supertypes stay ambiguous)
      if (exp.isNone || exp == some .any) && !ambiguousJoin (← get).env a b then return .any
      eerr p s!"the branches have different types: {a.show} and {b.show}"


/-- `M[k]` on the map in slot `tm` with the key in slot `tk`: the value of the
    first pair whose key equals `k` (fails when there is none). `tp` is a
    slot for the pairs. -/
def mapLookup (tm tk tp : Nat) : Expr :=
  .prim .index [.forE tp (.local tm) (.prim .eq [.prim (.tupGet 0) [.local tp], .local tk])
      (.prim (.tupGet 1) [.local tp]), .lit (.int 0)]

/-- The position of key `k` (slot `tk`) in the map in slot `tm` (fails when absent). -/
def mapFind (tm tk ti : Nat) : Expr :=
  .prim .index [.forE ti (.prim .range [.lit (.int 0), .prim .sub [.prim .len [.local tm], .lit (.int 1)]])
      (.prim .eq [.prim (.tupGet 0) [.prim .index [.local tm, .local ti]], .local tk]) (.local ti),
    .lit (.int 0)]

/-- Insert or update `(k, v)` (slots `tk`, `tv`) in the map in slot `tm`, in
    place when the key exists, at the end otherwise (Book of Verse §9.3). -/
def mapPut (tm tk tv ti tidx : Nat) : Expr :=
  let pair := Expr.prim .mkTup [.local tk, .local tv]
  .ite (.seq (.assign tidx (mapFind tm tk ti)) (.assign tm (.prim .arrSet [.local tm, .local tidx, pair])))
    (.lit .void)
    (.seq (.assign tm (.prim .concat [.local tm, .prim .mkArr [pair]])) (.lit .void))

/-- The position of a field in its struct. -/
def fieldIndex (fs : List (String × Ty × Option SExpr)) (f : String) : Option (Nat × Ty) :=
  ((fs.zip (List.range fs.length)).find? (·.1.1 == f)).map fun ((_, t, _), k) => (k, t)

/-- Write `v` to field `f` (of type `t`, at position `k` in `sn`) of the
    object in slot `obj`, of static type `sn(targs)`: in place when the field
    has one position in every class below (`k`, or another for an interface
    listed after a class or interface with fields), otherwise after a test of
    the object's class, as a read does (an interface's field can sit at
    different positions in the classes implementing it). The value is `v`. -/
def setFieldAt (env : TyEnv) (p : Pos) (sn : String) (targs : List Ty) (obj : Nat) (f : String) (k : Nat) (t : Ty)
    (v : Expr) : EM Expr := do
  let ds := env.concreteBelow sn
  let pos := ds.map fun d => ((fieldIndex (env.fields d []) f).map (·.1)).getD k
  -- (where every class below has it, so does every placeholder below, #157,
  -- and with one type in all of them, #205)
  let p0 := pos.headD k
  let tyOK := env.fieldTyAgrees sn targs f
  -- (not through views: each class's setter, #351)
  if tyOK && pos.all (· == p0) && !env.viewed.contains sn then return .heap (.set p0) [.local obj, v]
  if let some d := ds.find? fun d => !env.sameCore d sn && (env.fieldAcc.idxOf? (d, f)).isNone then
    if !tyOK then
      eerr p s!"field '{f}' of {sn} has another type in {d}, which takes it from another interface, and {d} has type parameters that {sn} does not have: setting it through {sn} is not supported yet (#205)"
    eerr p s!"field '{f}' of {sn} sits at different places in the classes below it, and {d} has type parameters that {sn} does not have: setting it is not supported yet (#53, #157)"
  let tv ← fresh t
  let mut acc : Expr := .prim .userErr []   -- no class: unreachable
  let mut refined := false
  for (d, kd) in (ds.zip pos).reverse do
    match env.fieldAcc.idxOf? (d, f) with
    | some i =>
      -- (a class that fixes the type arguments: its setter, under the
      -- refinement, #157)
      acc := .ite (.heap (.isTag [env.tagOf d]) [.local obj]) (.call (env.fieldAccBase + 2 * i + 1) [.local obj, .local tv]) acc
      refined := true
    | none =>
      let yd ← fresh (.struct d (env.argsAt sn targs d))
      acc := .ite (.assign yd (.heap (.isTag [env.tagOf d]) [.local obj])) (.heap (.set kd) [.local yd, .local tv]) acc
  if refined then
    -- (checked against the field's type, as the refined calls need one)
    let y ← fresh t
    return .seq (.assign tv v) (.assign y acc)
  return .seq (.assign tv v) acc

/-- The UTF-8 encoding of the char32 in slot `tc`, a Unicode scalar value:
    its one to four bytes as chars, each looked up in the table of the 256
    byte values (Verse Core has no conversion from int to char; the lookups
    and the divisions cannot fail, but are guarded so that the checker sees
    no failure). -/
def utf8Of (tc : Nat) : EM Expr := do
  let table : Expr := .lit (.arr ((List.range 256).map Value.char).toArray)
  let int (i : Int) : Expr := .lit (.int i)
  let chr (b : Expr) : EM Expr := do
    let tch ← fresh .char
    return .ite (.assign tch (p2 .index table b)) (.local tch) (.prim .userErr [])
  let c := Expr.local tc
  let (a, b, d, e, r, r2) := (← fresh .int, ← fresh .int, ← fresh .int, ← fresh .int, ← fresh .int, ← fresh .int)
  let q (x : Expr) (n : Int) := p2 .quotient x (int n)
  let m (x : Expr) (n : Int) := p2 .modulo x (int n)
  let seqs : List Expr → Expr := fun es => (es.dropLast).foldr .seq (es.getLast?.getD (.lit .void))
  let plus (k : Int) (x : Nat) := p2 .add (int k) (.local x)
  let one := Expr.prim .mkArr [← chr c]
  let two := Expr.prim .mkArr [← chr (plus 192 a), ← chr (plus 128 b)]
  let three := Expr.prim .mkArr [← chr (plus 224 a), ← chr (plus 128 b), ← chr (plus 128 d)]
  let four := Expr.prim .mkArr [← chr (plus 240 a), ← chr (plus 128 b), ← chr (plus 128 d), ← chr (plus 128 e)]
  return .ite (p2 .lt c (int 0x80)) one
    (.ite (seqs [p2 .lt c (int 0x800), .assign a (q c 64), .assign b (m c 64)]) two
    (.ite (seqs [p2 .lt c (int 0x10000), .assign a (q c 4096), .assign r (m c 4096),
        .assign b (q (.local r) 64), .assign d (m (.local r) 64)]) three
    (.ite (seqs [.assign a (q c 262144), .assign r (m c 262144), .assign b (q (.local r) 4096),
        .assign r2 (m (.local r) 4096), .assign d (q (.local r2) 64), .assign e (m (.local r2) 64)]) four
      (.prim .userErr []))))

/-- A Verse Core type that several front-end types have: one with an
    `int` (also a char32 or an enum), a tuple (also a struct), or a type
    variable. -/
partial def _root_.OpenVerse.VTy.shared : VTy → Bool
  | .int | .tup _ | .var _ => true
  | .arr t | .opt t => t.shared
  | _ => false

/-- `ToString` for interpolation. -/
def toStringOf (p : Pos) (r0 : R) : EM Expr := do
  let r := widenR (← get).env r0
  match r.ty with
  | .char32 => do
    let tc ← fresh .int
    return .seq (.assign tc r.e) (← utf8Of tc)
  | .int | .char | .float => pure (.prim .toStr [r.e])
  | .arr .char => pure r.e
  | t => eerr p s!"no ToString for {t.show} (Verse defines it for int, float, char, char32 and string)"

/-- The names that are values here, for lifting choices (#208): variables
    in scope, `Self` and its fields. -/
def choiceValues (ctx : Ctx) (n : String) : Bool :=
  (ctx.lookup n).isSome || n == "Self" ||
    (match ctx.selfClass with | some c => (ctx.types.fields c).any (·.1 == n) | none => false)

/-- `n.m` reads a field here (a variable or `Self` of a class or struct
    type that has one), for lifting choices: the field is read whole before
    the choice, while a method call's receiver only is (#208). -/
def choiceField (ctx : Ctx) (n m : String) : Bool :=
  let ty? : Option Ty := if n == "Self" then ctx.selfClass.map (fun c => .struct c []) else (ctx.lookup n).map (·.ty)
  match ty? with
  | some (.struct c _) => (ctx.types.fields c).any (·.1 == m)
  | _ => false

/-- Contextual types travel with a lifted operand when a later pass moves
    its clause into a continuation. The metadata has no runtime expressions. -/
def ConstructHint.toExpr (h : ConstructHint) : SExpr :=
  let p := h.pos
  let entries (xs : List (String × Ty)) := xs.map fun (n, t) =>
    SExpr.decl p n (some t.toSTy) false (.tuple p [])
  .app p (.ident p "$constructHint")
    [.str p [.text h.origin], .str p [.text h.frame], .str p [.text h.site],
     .block p (h.defaults.map fun (n, f) => .tuple p [.str p [.text n], .str p [.text f]]),
     .block p (entries h.inputs), .block p (entries h.aliases),
     .decl p "$instance" (some h.ty.toSTy) false (.tuple p [])] false

/-- For `Choice.prepare` (#283): a struct's or class's fields in declaration
    order, the order its constructions evaluate them in, each with whether
    its default is more than a literal. -/
def choiceOrder (ctx : Ctx) (n : String) : Choice.FieldOrder :=
  { fields := if (ctx.types.structs.lookup n).isNone then [] else
      (ctx.types.fields n).map fun (f, _, d) => (f, match d with
        | some d => !Choice.stable (fun _ => true) d
        | none => false)
    probe := ctx.constructProbe, inlineSite := ctx.inlineScopes.headD "",
    origin := ctx.constructOrigin.getD ctx.frameName,
    hints := ((ctx.constructHints.getD []).filter (·.name == n)).map ConstructHint.toExpr }

/-- Lift-generated operand names retain their position and kind between
    the probe and real pass; inserting a default changes their counter only. -/
def constructLocalName (n : String) : String :=
  let suffix := (n.splitOn "@").getLast!
  let parts := suffix.splitOn "_"
  let numeric := fun (s : String) => s.toNat?.isSome
  let lifting := if n.contains '@' then parts.length == 3 && parts.all numeric else
    match parts with
    | [head, col, counter] =>
      numeric col && numeric counter &&
        ["$t", "$c", "$b", "$s", "$dv"].any fun k => head.startsWith k && numeric (head.drop k.length).toString
    | _ => false
  if !lifting then n else String.intercalate "_" (n.splitOn "_").dropLast

def constructHint (ctx : Ctx) (p : Pos) (n site : String) (ty : Ty) : ConstructHint :=
  { pos := p, name := n, site, frame := ctx.frameName,
    origin := ctx.constructOrigin.getD ctx.frameName, defaults := ctx.defaults,
    selfClass := ctx.selfClass, tag := ctx.liftTag,
    inputs := ctx.locals.map fun l => (constructLocalName l.name, l.ty),
    aliases := ctx.types.tvars, ty }

def constructInstance (ctx : Ctx) (p : Pos) (n : String) (ts : List STy) (site : String)
    (origin : String) (metadata : List SExpr) : EM Ty := do
  if !ts.isEmpty || ((ctx.types.sparams.lookup n).getD []).isEmpty then
    return ← resolveTy ctx.types p (if ts.isEmpty then .name n else .app n ts)
  let inputs := ctx.locals.map fun l => (constructLocalName l.name, l.ty)
  let hints := (ctx.constructHints.getD []).filter fun h =>
    h.pos.line == p.line && h.pos.col == p.col && h.pos.file == p.file && h.name == n &&
    h.site == site && h.frame == ctx.frameName && h.origin == origin && h.defaults == ctx.defaults &&
    h.selfClass == ctx.selfClass && h.tag == ctx.liftTag &&
    h.inputs.all (inputs.contains ·) && h.aliases.all (ctx.types.tvars.contains ·)
  let mut tys := (hints.map (·.ty)).eraseDups
  if tys.isEmpty then
    -- A continuation keeps only the lexical values/types its body needs.
    -- Check every retained input against the original instance, and require
    -- one resulting construction type across all compatible candidates.
    for entry in metadata do
      let .app hp (.ident _ "$constructHint")
          [.str _ [.text root], .str _ [.text frame], .str _ [.text active], .block _ defaults,
           .block _ ins, .block _ aliases, .decl _ "$instance" (some ty) _ _] false := entry | continue
      if hp.line != p.line || hp.col != p.col || hp.file != p.file || root != origin || frame != ctx.frameName || active != site then continue
      let ds := defaults.filterMap fun
        | .tuple _ [.str _ [.text c], .str _ [.text f]] => some (c, f)
        | _ => none
      if ds != ctx.defaults then continue
      let check (xs : List SExpr) (available : List (String × Ty)) : EM Bool := do
        for x in xs do
          let .decl _ key (some t) _ _ := x | return false
          let actual := available.filter (·.1 == key) |>.map (·.2)
          if !actual.isEmpty then
            let expected ← resolveTy ctx.types p t
            if !actual.contains expected then return false
        return true
      let candidate ← tryCatch (do
        if !(← check ins inputs) || !(← check aliases ctx.types.tvars) then return none
        return some (← resolveTy ctx.types p ty)) (fun _ => pure none)
      if let some t := candidate then if !tys.contains t then tys := tys ++ [t]
  match tys with
  | [t] => return t
  | [] => eerr p s!"cannot infer the type arguments of {n} before its field choices"
  | _ => eerr p s!"the field choices of {n} have different construction instances here"

/-- Specialize a moved clause's construction metadata before its lexical
    type aliases disappear. Future refining/default scopes keep their own
    records until that scope is lifted. Only lexical names (not normalized
    lifting counters) constrain this transfer; later prefixes add temporaries. -/
def pruneConstructHints (ctx : Ctx) (target : String) (body : SExpr) : SExpr :=
  Choice.mapE (fun
    | .app p (.ident _ "$constructHints") [.block bp entries] false =>
      let entries := entries.filterMap fun entry => match entry with
        | .app hp f [.str op [.text origin], .str sp [.text scope], site,
            .block dp defaults, .block ip inputs, .block ap aliases, result] false =>
          let ds := defaults.filterMap fun
            | .tuple _ [.str _ [.text c], .str _ [.text n]] => some (c, n)
            | _ => none
          if scope != ctx.frameName || ds != ctx.defaults then some entry else
          let agrees (xs : List SExpr) (available : List (String × Ty)) : Bool := xs.all fun
            | .decl q key (some ty) _ _ =>
              let actual := available.filter (·.1 == key) |>.map (·.2)
              if actual.isEmpty then true else
                match (resolveTy ctx.types q ty).run { env := ctx.types } with
                | .ok (t, _) => actual.any fun a =>
                  let a := a.subst ctx.types.tvars
                  !a.params.isEmpty || !t.params.isEmpty || a == t
                | .error _ => true
            | _ => false
          if !agrees inputs (ctx.locals.map fun l => (l.name, l.ty)) || !agrees aliases ctx.types.tvars then none else
            some (.app hp f [.str op [.text origin], .str sp [.text target], site,
              .block dp defaults, .block ip inputs, .block ap aliases, result] false)
        | _ => none
      some (.app p (.ident p "$constructHints") [.block bp entries] false)
    | _ => none) body

/-- Keep a class cast with its branch until its refinement can be applied.
    A receiver bound by earlier clauses need not be in the context yet. -/
def choiceHasCast (ctx : Ctx) (i : SExpr) : Bool :=
  (Choice.arms i).any fun (cs, _) => cs.any fun clauses => clauses.any fun
    | .decl _ _ none false (.app _ (.ident _ target) [_] true) => ctx.types.classes.contains target
    | .decl _ _ none false (.app _ (.ident _ marker) [ .app _ (.ident _ target) [_] true ] false) =>
      ["$methodCast", "$methodCase"].contains marker && ctx.types.classes.contains target
    | _ => false

/-- A generated method dispatch can omit a class that cannot inhabit its
    receiver's current type arguments. Other cases become ordinary refining
    casts, kept with their selected implementation. Receivers are already
    bound once by the dispatch's parameter prefix. -/
partial def pruneMethodCases (ctx : Ctx) : SExpr → SExpr
  | e@(.ite p [.decl dp d none false (.app _ (.ident _ marker)
      [cast@(.app _ (.ident _ target) [.ident _ x] true)] false)] body (some next)) =>
    if !["$methodCast", "$methodCase"].contains marker then e else
    let next := pruneMethodCases ctx next
    let possible := match ctx.lookup x with
      | some l => match l.ty.subst ctx.types.tvars with
        | .struct source args => ((ctx.types.concreteBelow source).filter fun c =>
            if marker == "$methodCase" then c == target else ctx.types.isSub c target).any fun c =>
          ((ctx.types.viewArgs? source c (ctx.types.coreArgs source args) (rigid := false)).bind fun as =>
            ctx.types.refineComparable? [] (ctx.types.comparableArgs c as)).isSome
        | _ => true
      | none => true
    if possible then .ite p [.decl dp d none false cast] body (some next)
    -- A covariant call has an explicit static result type. Drop an exact
    -- class case outside that receiver's domain, including in kept bodies;
    -- synthesizing a failing value here would make a pure checked body fail.
    else if marker == "$methodCase" then next
    -- Keep an if and its unique binder even when it cannot select a body:
    -- later exclusive lowering still needs a case boundary and a known type.
    else .ite p [.decl dp d none false (.block p [.query p (.ident p "false"), .ident p x])]
      (.app p (.ident p "$methodMiss") [] false) (some next)
  | e => e

/-- Normalize a dispatch condition after its receiver prefix is typed. -/
def pruneMethodBinding (ctx : Ctx) : SExpr → SExpr
  | .decl p n ty v (.app q f@(.ident _ "$branchChoice") [i] false) =>
    let i := pruneMethodCases ctx i
    match i with
    | .ite .. => .decl p n ty v (.app q f [i] false)
    | _ => .decl p n ty v i
  | e => e

/-- A local named `n` may be declared here: Verse has no shadowing. -/
def checkNewLocal (ctx : Ctx) (p : Pos) (n : String) : EM Unit := do
  if ctx.lookup n |>.isSome then
    let n := Choice.shownName n
    eerr p s!"'{n}' is already defined; Verse does not allow shadowing (use set {n} = … for a var)"
  -- (nor a soft built-in's: a local cannot hide one, #132)
  if (ctx.sig? n).isSome || builtins.contains n || softBuiltins.contains n then
    eerr p s!"'{n}' is already the name of a function or constant"
  if let some c := ctx.selfClass then
    if (ctx.types.fields c).any (·.1 == n) || ctx.hasMethod c n ||
        ((ctx.types.methodOverloads.lookup n).map (·.any (ctx.hasMethod c ·))).getD false then
      eerr p s!"'{n}' is already a field or method of {c}; Verse does not allow shadowing"

/-- (#335) Whether `e` writes one of the type parameters `tps`: in a written
    type, a construction's, or as a name. Conservative. -/
partial def writesTps (tps : List String) (e : SExpr) : Bool :=
  if tps.isEmpty then false else match e with
  | .app _ (.ident _ "$constructHints") _ false => false
  | e =>
    (match e with
    | .decl _ _ (some t) _ _ => Choice.styMentions tps t
    | .construct _ n ts _ => tps.contains n || ts.any (Choice.styMentions tps)
    | .structDef _ _ fs => fs.any fun (_, t, _, _) => Choice.styMentions tps t
    | .refineDef _ _ t _ => Choice.styMentions tps t
    | .ident _ n => tps.contains n
    | _ => false) || e.children.any (writesTps tps)

/-- A helper retains the source context's restrictions and dependency stack,
    while its generated control flow still owns its own loops and exits. -/
def sourceContextOf (ctx : Ctx) : Choice.SourceContext := {
  inCtor := ctx.inCtor, inParamDefault := ctx.inParamDefault,
  inBlock := ctx.inBlock, inDefer := ctx.inDefer,
  inDefaultCheck := ctx.inDefaultCheck, inRepeat := ctx.inRepeat,
  inChoice := ctx.inChoice, inArm := ctx.inArm, inBranch := ctx.inBranch,
  defaults := ctx.defaults }

def sourceContextKey (ctx : Ctx) : String :=
  let scope := sourceContextOf ctx
  if scope == ({} : Choice.SourceContext) then "" else "_source:" ++ reprStr scope

/-- Refined helpers keep their source copy tag and context identity separate. -/
def refineTagOf (ctx : Ctx) : String :=
  let source := sourceContextKey ctx
  let inputs := ctx.locals.filterMap fun l =>
    if (Choice.shownName l.name).startsWith "$" then none else some (l.name, l.ty, l.mutable)
  let typing := reprStr (ctx.types.tvars, inputs, ctx.retTy, ctx.inlineScopes)
  ctx.refineScope ++ ctx.liftTag ++ (if source.isEmpty then "" else s!"$source{(source ++ typing).hash}")

def firstReturns (rest : List SExpr) : Bool :=
  (Refine.findPart (fun | .ret .. => true | _ => false) false (.block { line := 0, col := 0 } rest)).isSome

/-- The source return type remains separate from a helper's packet type. -/
def firstReturnType (ctx : Ctx) : STy :=
  let ty := match ctx.refineExits.ret with
    | some (some (_, ty), _) => ty
    | some (none, _) => .name "void"
    | none => match ctx.forReturnSlot.bind ctx.lookup with
      | some { ty := .opt t, .. } => t.toSTy
      | _ => ctx.retTy.toSTy
  ty.substNames (ctx.types.tvars.map fun (n, t) => (n, t.toSTy))

def firstReturnKey (ctx : Ctx) (rest : List SExpr) : String :=
  if !firstReturns rest then "" else
    let ty := firstReturnType ctx
    let bounds := Ty.mergeParamBounds ((ctx.types.tvars.map (·.2)).flatMap Ty.paramsC)
      |>.filter fun (n, _) => Choice.styMentions [n] ty
    "_return:" ++ reprStr (ty, bounds)

/-- Normal success has all bound names. A return instead has the saved
    operand; both outcomes copy back captures before the caller proceeds. -/
def firstResult (p : Pos) (name : String) (binds sets : List Local) (source : Option Ty) :
    STy × SExpr × Option Choice.FirstReturn :=
  let values := binds.map fun l => SExpr.ident p l.name
  let copied := sets.map fun l => SExpr.ident p l.name
  match source with
  | none => (.tup ((binds ++ sets).map (·.ty.toSTy) ++ [.name "logic"]),
      .tuple p (values ++ copied ++ [.ident p "true"]), none)
  | some ty =>
    let ret := STy.tup (.opt (.tup (binds.map (·.ty.toSTy))) :: sets.map (·.ty.toSTy) ++ [.opt ty.toSTy, .name "logic"])
    let value := if ty == .void then none else some (name ++ "$return")
    let saved := (value.map (SExpr.ident p ·)).getD (.tuple p [])
    let normal := SExpr.tuple p (.optionLit p (.tuple p values) :: copied ++ [.ident p "false", .ident p "true"])
    let normal := SExpr.decl p (name ++ "$normal") (some ret) false normal
    let returned := SExpr.tuple p (.ident p "false" :: copied ++ [.optionLit p saved, .ident p "true"])
    (ret, normal, some { ty := ty.toSTy, value, packet := [returned] })

/-- Update source captures before returning or exposing the normal bindings. -/
def firstUnpack (p : Pos) (l : Choice.FirstLift) (packet : String) : List SExpr :=
  let get (base : String) (j : Nat) := SExpr.app p (.ident p base) [.int p (j : Int)] false
  if l.returnExit.isNone then
    l.binds.zipIdx.map (fun (n, i) => .decl p n none (l.varBinds.contains n) (get packet i)) ++
      l.sets.zipIdx.map (fun (n, j) => .set p (.ident p n) none (get packet (l.binds.length + j)))
  else
    let returned := packet ++ "$returned"
    let normal := packet ++ "$normal"
    l.sets.zipIdx.map (fun (n, j) => .set p (.ident p n) none (get packet (j + 1))) ++
      [.ite p [.decl p returned none false (.query p (get packet (l.sets.length + 1)))]
        (.ret p (some (.ident p returned))) none,
        .decl p normal none false (.query p (get packet 0))] ++
      l.binds.zipIdx.map (fun (n, j) => .decl p n none (l.varBinds.contains n) (get normal j))

/-- A lazy helper owns its producer and the complete prepared suffix. That
    suffix changes when a composed choice is replaced by a continuation call;
    source position and captured names alone would reuse the previous contract.
    The named type instances also distinguish an inlined body's output types
    even when its producer parameters and captures have identical types. -/
def firstKey (ctx : Ctx) (p : Pos) (lp : List SExpr) (b : String) (bty : Option STy)
    (rest : List SExpr) : String :=
  let written := SExpr.block p (lp ++ rest)
  let inputs := (Choice.namesUsed written).eraseDups.filterMap fun n =>
    (ctx.lookup n).map fun l => (n, l.ty, l.mutable)
  let aliases := ctx.types.tvars.filter fun (n, _) =>
    writesTps [n] written || ((bty.map (Choice.styMentions [n])).getD false)
  reprStr (p, b, bty, lp, rest, inputs, aliases, ctx.selfClass, ctx.liftTag, ctx.inlineScopes) ++ sourceContextKey ctx ++ firstReturnKey ctx rest

/-- A cast `T[X]`, `X` of type `xty`, that holds only under a refinement of
    the code's type parameters (#243): `T` fixes or repeats type arguments
    of `X`'s class, which agree with `X`'s only when they are unified (as
    `elabCast` refuses). `X`'s class and type arguments, `T`'s type
    arguments, the classes the cast tests for, and the equations of the
    refinement; `none` for any other cast. -/
def refiningCast? (env : TyEnv) (T : String) (xty : Ty) (avoid : List String := []) :
    Option (String × List Ty × List Ty × List String × List (Ty × Ty) × List (String × String × Bool)) := do
  let .struct S sargs := xty | none
  if !env.classes.contains S || !env.classes.contains T then none
  if (env.sparams.lookup T).isNone && (env.coreArgs T []).isEmpty then none
  if !(env.isSub S T || env.isSub T S) then none
  let rargs := env.coreArgs S sargs
  let common := (env.concreteBelow S).filter (env.isSub · T)
  if common.isEmpty then none
  let tv := env.coreVars T
  -- (#351: an object referred to through views relates its type arguments
  -- to `T`'s through `S`'s view of `T`, never by position)
  let viewedS := env.viewed.contains S
  if !viewedS && tv.length == rargs.length && tv.all (fun (v, _) => !v.startsWith "$arg") then
    -- (#243: `T`'s Verse Core type arguments are its own type parameters,
    -- as many as the object's: those, as the object's type gives them)
    let targs := if env.isSub S T then env.upArgs S sargs T else env.argsBelow S sargs T
    let cargs := env.coreArgs T targs
    let bounds := env.refineComparable? [] (env.comparableArgs T targs)
    if bounds.isNone then none else
    if cargs == rargs && bounds.any List.isEmpty then none
    let eqs := rargs.zip cargs
    if (Ty.unifyEqs (fun _ _ => none) [] eqs).isNone then none
    some (S, sargs, targs, common, eqs, [])
  else
    -- (#250: more, or not its type parameters as a whole: each of `T`'s
    -- type parameters fresh (not a name of `avoid`), unified with the
    -- object's type arguments, the fresh ones bound first; those left
    -- unbound are opened, as comparable as the parameters they stand for)
    if env.isSub S T then none
    let ps := (env.sparams.lookup T).getD []
    let names : List String := ps.foldl (fun acc (v, _) => Id.run do
      let mut n := v ++ "'"
      while avoid.contains n || acc.contains n do n := n ++ "'"
      return acc ++ [n]) []
    let targs := (ps.zip names).map fun ((_, c), n) => Ty.param n c
    let cargs := env.coreArgs T targs
    if !viewedS && cargs.length < rargs.length then none
    let eqs := if viewedS then (env.viewOf S T cargs).zip rargs
      else (cargs.take rargs.length).zip rargs
    let some μ := Ty.unifyEqs (fun _ _ => none) [] eqs | none
    let opened := (ps.zip names).filterMap fun ((v, c), n) =>
      if (μ.lookup n).isSome then none else some (n, v, c)
    -- (an interface has no hidden fields to read opened ones from, #53:
    -- such a cast is a plain one, which refuses unknown type arguments)
    if (env.info T).isIface && !opened.isEmpty then none
    -- (nothing to refine, to open, nor past the object's: a plain cast;
    -- through a view, the object's type arguments come from the dispatch,
    -- as a plain cast does not give them, #351)
    let bounds := env.refineComparable? μ (env.comparableArgs T targs)
    if bounds.isNone then none else
    if !viewedS && cargs.length == rargs.length && opened.isEmpty && μ.all (names.contains ·.1) &&
        (bounds.getD []).all (names.contains ·.1) then none
    some (S, sargs, targs, common, eqs, opened)

/-- Unify a refining cast's equations, preserving comparable opened types. -/
def castRefinement? (env : TyEnv) (eqs : List (Ty × Ty)) (opened : List (String × String × Bool))
    (required : List Ty := []) :
    Option (List (String × Ty) × List (String × String × Bool)) := do
  let coreFields (n : String) (ts : List Ty) : Option (List Ty) :=
    if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
  let μ ← Ty.unifyEqs coreFields [] eqs
  let μ ← env.refineComparable? μ required
  let opened := opened.map fun (n, v, cmp) =>
    let refined := (Ty.param n cmp).subst μ
    (n, v, cmp || refined.comparable env)
  some (μ, opened)

/-- The implementation `(super:)M` reaches in a method of class `c`: what
    the class inherits for the method's slot (`(r:)M`'s, or every slot of
    `M`, implemented alike above it, or the class chain's). -/
def superImpl (ctx : Ctx) (p : Pos) (c m : String) : EM String := do
  -- in `(r:)m`, slot r; otherwise every slot of `m` (#70): what is above `c`
  -- implements them alike, or the class chain's implementation is the one
  let slots := match ctx.selfMethod with
    | some cur => match (cur.drop 1).toString.splitOn ":)" with
      | [r, m'] => if cur.startsWith "(" && m' == m then [r] else ctx.rootsOf c m
      | _ => ctx.rootsOf c m
    | none => ctx.rootsOf c m
  let ups := (ctx.types.supers c).drop 1
  let found := (slots.filterMap fun r => (ctx.types.slotImpls (ctx.implAt r m) ups r).head?).eraseDups
  let inClass := found.filter fun f => !(ctx.types.info ((f.splitOn ".").head!)).isIface
  match found, inClass with
  | [f], _ => pure f
  | [], _ => eerr p s!"nothing above {c} implements '{m}'"
  | _, [f] => pure f
  | f :: g :: _, _ =>
    eerr p s!"(super:){m} is ambiguous here: {f} and {g} implement it for different interfaces above {c}; call it from a qualified (i:){m}"

/-- What, in the branch of a cast that refines type arguments, would not
    mean the same once the branch is a function of its own (#243): its
    position and what it is. `muts` are the `var`s it uses from outside. -/
def refineBranchWhy? (_ctx : Ctx) (_p : Pos) (body : SExpr) (muts : List String) (allowEsc : Bool := false) :
    Option (Pos × String) :=
  if let some e := (if allowEsc then none else Refine.findPart (fun | .ret .. => true | _ => false) false body) then
    some (e.pos, "it cannot have a return yet")
  else if let some e := (if allowEsc then none else Refine.findPart (fun | .brk _ => true | _ => false) true body) then
    some (e.pos, "it cannot have a break that leaves it yet")
  else if let some e := Refine.findPart (fun
      | .set _ l _ _ => (Choice.rootName? l).any muts.contains
      | _ => false) false body then
    some (e.pos, "it cannot set a var from outside it yet")
  else none

/-- Statements every path of which ends in a `return` or a `break` (#243). -/
partial def escapesAlways (ss : List SExpr) : Bool :=
  match ss.getLast? with
  | some (.ret ..) => true
  | some (.ite _ _ t (some u)) => escapesAlways (Choice.stmtsOf t) && escapesAlways (Choice.stmtsOf u)
  | e => e.any Refine.isBreak

/-- How a refined branch's value leaves its function (#243): not at all
    (the `if` is `void`), as it is (at its type when known: the branch
    always ends), as an option (it may also leave by a `return` or
    `break`), or not, the branch always leaving, so the `else`'s value is
    taken after the `if`. -/
inductive ExitVal where
  | none
  | raw (t : Option STy)
  | opt (t : STy)
  | elseAfter

/-- (#243) `if (D := T[x]) then B else E` whose branch `B`, compiled as a
    function of its own, sets `var`s from outside it (`vars`), has a
    `return`, or a `break` that leaves it: every way it leaves becomes a
    value of a tuple of what it says (an option of the enclosing
    function's result, `retS`, or a `logic` for a `void` one; a `logic`
    for a `break`; its value, as `vm` has it) and the values of copies of
    those `var`s (`$exit…'N`, shown as written), which it uses in their
    place; the `else` gives the `var`s' own. After the `if`, the caller
    sets the `var`s from the tuple, then returns or breaks as it says, else
    takes the value. Each value is bound, at its type, before it goes in an
    option, so that its failure is the branch's. Gives the new branch and
    else, the tuple's type when known, the name the `if`'s value is bound
    to, what follows it, and how the lifted function packs explicit exits. -/
def refineExits (p : Pos) (body : SExpr) (elseE : Option SExpr) (vars : List (String × STy))
    (hasRet : Bool) (brkPart : Option SExpr) (retS : Option STy) (vm : ExitVal) :
    SExpr × SExpr × Option STy × String × List SExpr × Refine.Exits :=
  let tag := s!"$exit{p.line}_{p.col}"
  let cp (n : String) : String := s!"{tag}'{n}"
  let ren := vars.map fun (n, _) => (n, cp n)
  let hasBrk := brkPart.isSome
  let retC : List STy := if hasRet then [retS.map STy.opt |>.getD (.name "logic")] else []
  let brkC : List STy := if hasBrk then [.name "logic"] else []
  let valC : List (Option STy) := match vm with
    | .raw t => [t]
    | .opt t => [some (.opt t)]
    | _ => []
  let comps : List (Option STy) := (retC ++ brkC).map some ++ valC ++ vars.map (some ·.2)
  let tupS : Option STy := if comps.all (·.isSome) then
      some (match comps.filterMap id with | [c] => c | cs => .tup cs) else none
  let n := comps.length
  let rr := s!"{tag}'r"
  let rx := s!"{tag}'rx"
  let vx := s!"{tag}'vx"
  let mk (retV : List SExpr) (brk : Bool) (val? : Option SExpr) (varsV : List SExpr) : List SExpr :=
    let brkV : List SExpr := if hasBrk then [.ident p (if brk then "true" else "false")] else []
    let (pre, valV) : List SExpr × List SExpr := match vm, val? with
      | .raw t, some v => ([.decl p vx t false v], [.ident p vx])
      | .opt t, some v => ([.decl p vx (some t) false v], [.optionLit p (.block p [.ident p vx])])
      | .opt _, none => ([], [.ident p "false"])
      | .raw _, none => ([], [.tuple p []])
      | _, _ => ([], [])
    let val := match retV ++ brkV ++ valV ++ varsV with | [v] => v | vs => .tuple p vs
    pre ++ [.decl p rr tupS false val, .ident p rr]
  let copiesV := vars.map fun (n, _) => SExpr.ident p (cp n)
  let outsV := vars.map fun (n, _) => SExpr.ident p n
  let copies := vars.map fun (n, t) => SExpr.decl p (cp n) (some t) true
    (.app p (.ident p "$refineCopyIn") [.ident p n] false)
  let noRet : List SExpr := if hasRet then [.ident p "false"] else []
  let done (val? : Option SExpr) (varsV : List SExpr) := SExpr.block p (mk noRet false val? varsV)
  let exits : Refine.Exits := {
    ret := if hasRet then
      let v := if retS.isSome then SExpr.optionLit p (.block p [.ident p rx]) else .ident p "true"
      some (retS.map (rx, ·), mk [v] false none copiesV) else none
    brk := if hasBrk then some (mk noRet true none copiesV) else none }
  let always := escapesAlways (Choice.stmtsOf body)
  let body := Choice.renameE ren body
  -- Mark breaks that leave this lift. A nested lift forwards the marker
  -- after copying back into this frame, just as it forwards a return.
  let body := Choice.mapE (fun
    | .brk q => some (Refine.liftedBreak q)
    | l@(.loop ..) => some l
    | _ => none) body
  let ss := Choice.stmtsOf body
  let (stmts, value) : List SExpr × Option SExpr := match vm, ss.getLast? with
    | .raw _, some (.decl q y _ _ _) | .opt _, some (.decl q y _ _ _) => (ss, some (.ident q y))
    | .raw _, some l | .opt _, some l => (ss.dropLast, some l)
    | _, _ => (ss, none)
  let hasDefer := ss.any fun
    | .app _ (.ident _ "$defer") [_] false => true
    | _ => false
  let endV : List SExpr :=
    if always then ss
    else if vars.isEmpty || !hasDefer then stmts ++ [done value copiesV]
    -- Leave the scope of the branch's defers before reading the copied slots.
    -- A branch value is evaluated inside that scope and saved across cleanup.
    else match value with
      | some v => [done (some (.block p (stmts ++ [v]))) copiesV]
      | none => [.block p stmts, done none copiesV]
  let thenB := SExpr.block p (copies ++ endV)
  let elseB : SExpr := match vm, elseE with
    | .raw _, some e | .opt _, some e => done (some e) outsV
    | .none, some e => .block p [e, done none outsV]
    | _, _ => done none outsV
  let t := s!"{tag}'t"
  let get (i : Nat) : SExpr := if n == 1 then .ident p t else .app p (.ident p t) [.int p (i : Int)] false
  let nRB := retC.length + brkC.length
  let ci := nRB + valC.length
  let rv := s!"{tag}'rv"
  let vv := s!"{tag}'vv"
  let brk := match brkPart with
    | some (.brk _) | none => SExpr.brk p
    | some _ => Refine.liftedBreak p
  let writes := vars.zipIdx.map fun ((nm, _), k) => SExpr.set p (.ident p nm) none
    (.app p (.ident p "$refineCopyOut") [get (ci + k)] false)
  let after : List SExpr := writes ++
    (if hasRet then [if retS.isSome then .ite p [.decl p rv none false (.query p (get 0))] (.ret p (some (.ident p rv))) none
      else .ite p [.query p (get 0)] (.ret p none) none] else []) ++
    (if hasBrk then [.ite p [.query p (get retC.length)] brk none] else []) ++
    [match vm, elseE with
      | .raw _, _ => get nRB
      | .opt _, _ => .ite p [.decl p vv none false (.query p (get nRB))] (.ident p vv) (some (.app p (.ident p "Err") [] false))
      | .elseAfter, some e => e
      | _, _ => .tuple p []]
  (thenB, elseB, tupS, t, after, exits)

/-- In a method of class `c`, the branch of a cast that refines (#243), with
    the members of `Self` it names bare (its fields and methods, not shadowed
    by a local) made `Self.member`, as the elaborator reads them: its
    function, of its own, takes `Self` as a parameter. A super call keeps
    its source method's lookup scope, including qualified slots and
    overload resolution, and explicitly captures `Self`. -/
partial def selfQualify (ctx : Ctx) (c : String) (e : SExpr) : SExpr :=
  let isMethod (n : String) : Bool := ctx.hasMethod c n ||
    ((ctx.types.methodOverloads.lookup n).map (·.any (ctx.hasMethod c ·))).getD false
  let isField (n : String) : Bool := (ctx.types.fields c).any (·.1 == n)
  let bound := Choice.localsOf e
  let free (n : String) : Bool := (ctx.lookup n).isNone && !bound.contains n && n != "Self"
  Choice.mapE (fun
    | e@(.app _ (.ident _ "$sourceSuper") _ false) => some e
    | .app p f@(.member _ (.ident _ "(super:)") _) args br =>
      some (.app p (.ident p "$sourceSuper")
        [.str p [.text c], .str p [.text (ctx.selfMethod.getD "")], .ident p "Self",
          .app p f (args.map (selfQualify ctx c)) br] false)
    | e@(.member p (.ident _ "(super:)") _) =>
      some (.app p (.ident p "$sourceSuper")
        [.str p [.text c], .str p [.text (ctx.selfMethod.getD "")], .ident p "Self", e] false)
    | .app p (.ident q n) args br =>
      if free n && (isMethod n || (isField n && !builtins.contains n && !softBuiltins.contains n)) then
        some (.app p (.member q (.ident q "Self") n) (args.map (selfQualify ctx c)) br)
      -- (a call of anything else keeps its head as written: a field named
      -- like a built-in, `Max(7, 3)`, is the built-in there, as elsewhere)
      else some (.app p (.ident q n) (args.map (selfQualify ctx c)) br)
    | .ident p n => if free n && (isField n || isMethod n) then some (.member p (.ident p "Self") n) else none
    | _ => none) e

/-- A continuation keeps the parameters of its inputs, results and written
    types. A parameter not determined by its inputs takes an explicit witness,
    so a type used only by a local annotation is still inferred at the call. -/
def contTypes (ctx : Ctx) (p : Pos) (inputs outputs : List Ty) (written : SExpr) :
    Except String (List TParam × List SParam × List SExpr) := do
  let inputTps := inputs.flatMap Ty.paramsC
  let writtenTys := ctx.types.tvars.filterMap fun (n, t) =>
    if writesTps [n] written then some t else none
  let tps := Ty.mergeParamBounds (inputTps ++ (outputs ++ writtenTys).flatMap Ty.paramsC)
  let extra := tps.filter fun (n, _) => !inputTps.any (·.1 == n)
  let available := (ctx.types.tvars.map (·.2)).flatMap Ty.paramsC
  if extra.any (fun (n, _) => !available.any (·.1 == n)) then
    throw "a continuation type parameter has no witness in this context"
  return (tps.map (fun (n, cmp) => { pos := p, name := n, constraint := if cmp then "comparable" else "type" }),
    extra.map (fun (n, _) => { name := s!"$type{n}", ty := .name n }),
    extra.map (fun (n, _) => .app p (.ident p "$witness") [.ident p n] false))

/-- (#246) The function of its own a lazily taken call where the first
    success is taken is compiled as, when what it runs once for all the
    values of an item has effects (`Choice.FirstLift`): from the call
    (`lp`, its binding `b`), the consumer's names before it (`ctx`) and
    after the clauses that follow it (`c2`, those clauses `rest`), and the
    effects all that has (`fxB`); or why it cannot be yet. -/
def firstLiftOf (ctx c2 : Ctx) (p : Pos) (g : String) (lp : List SExpr) (b : String) (bty : Option STy)
    (rest : List SExpr) (fxB : List (String × Pos × Option String)) (suspends : Bool) (vty : Ty)
    (instances : List (String × List (String × Ty)) := []) :
    Except String Choice.FirstLift := do
  let [_, .block _ ps, .block _ cls, .decl _ _ _ _ tail] := lp | throw "internal: a $loop marker"
  let key := firstKey ctx p lp b bty rest
  let written := SExpr.block p (lp ++ rest)
  -- Written types use the context's current instances, including inlined
  -- producer parameters and aliases from an enclosing refining cast.
  let σt := ctx.types.tvars.map fun (n, t) => (n, t.toSTy)
  let bty := bty.map (·.substNames σt)
  let cls := cls.map (Refine.substTypes σt)
  let tail := Refine.substTypes σt tail
  let rest := rest.map (Refine.substTypes σt)
  -- (in a method: the members of `Self` the clauses name bare, as members
  -- of `Self`, which the function takes as a parameter, as #243's do)
  let rest ← match ctx.selfClass with
    | some c =>
      pure (rest.map (selfQualify ctx c))
    | none => pure rest
  -- (a `return`, or a `break` that leaves them, would leave the function
  -- of its own, not the consumer's)
  let source ← if firstReturns rest then
      some <$> (resolveTy ctx.types p (firstReturnType ctx)).run' { env := ctx.types }
    else pure none
  if (Refine.findPart (fun | .brk _ => true | _ => false) true (.block p rest)).isSome then
    throw "where the clauses after it have a break that leaves them"
  if suspends then throw "as the clauses after it suspend"
  let pnames := ps.filterMap fun | .ident _ n => some n | _ => none
  let pls ← pnames.mapM fun n => match ctx.lookup n with
    | some l => pure l
    | none => throw s!"internal: parameter {n}"
  -- (the consumer's names the clauses after it use, in order of first use)
  let caps : List Local := (Choice.namesUsed (.block p rest)).eraseDups.filterMap fun n =>
    if pnames.contains n then none else ctx.lookup n
  let setNames := Choice.setsIn (.block p rest)
  let sets := caps.filter fun l => l.mutable && setNames.contains l.name
  -- (its own binding too: a call in the clauses of another such call's
  -- function, compiled as one too, binds only what that one gives)
  let binds := (b :: Choice.boundIn rest).eraseDups
  let bls ← binds.mapM fun n => match c2.lookup n with
    | some l => pure l
    | none => throw s!"internal: name {n}"
  let (tps, typeParams, typeArgs) ← contTypes ctx p ((pls ++ caps).map (·.ty))
    (vty :: bls.map (·.ty) ++ source.toList) written
  -- A type determined by the entry's inputs may be absent from another
  -- member's inputs. Every member must still infer the shared helper's
  -- type parameters, including those used only by a producer result.
  let memberInputs := instances.filterMap fun (h, σ) =>
    if h == g then none else (ctx.sig? h).map fun sig =>
      (sig.params.map (·.subst σ) ++ caps.map (·.ty)).flatMap Ty.params
  let missing := tps.filter fun tp => memberInputs.any (!·.contains tp.name) &&
    !typeParams.any (·.name == s!"$type{tp.name}")
  let typeParams := typeParams ++ missing.map (fun tp => ({ name := s!"$type{tp.name}", ty := .name tp.name } : SParam))
  let typeArgs := typeArgs ++ missing.map (fun tp => SExpr.app p (.ident p "$witness") [.ident p tp.name] false)
  let name := s!"$first{p.line}_{p.col}_{key.hash}" ++ (if p.file.isEmpty then "" else s!"_{p.file}")
  -- Every recursive edge, including a mutual member's, forwards the same
  -- witnesses; a type used only by the suffix has no producer argument.
  let capArgs := caps.map (fun l => SExpr.ident p l.name) ++ typeParams.map (fun sp => .ident p sp.name)
  -- (#283) a function of a strongly connected group: the others' too, one
  -- function each, named after this one's
  let (tail, members) : SExpr × List SExpr := match tail with
    | .app _ (.ident _ "$group") (t0 :: ms) false => (t0, ms)
    | t => (t, [])
  let mnames : List String := members.filterMap fun
    | .app _ (.ident _ "$member") (.ident _ h :: _) false => some h
    | _ => none
  let nameOf (h : String) : String := if h == g then name else s!"{name}_{h.replace "::" "_"}"
  let heap := ["reads", "writes", "allocates"].filter fun k =>
    fxB.any (·.1 == k) || ((g :: mnames).any fun h => ((ctx.sig? h).map (·.fx.contains k)).getD false)
  let capPs : List SParam :=
    caps.map fun l => { name := if sets.any (·.name == l.name) then s!"{l.name}$in" else l.name, ty := l.ty.toSTy }
  let params : List SParam := pls.map (fun l => { name := l.name, ty := l.ty.toSTy }) ++ capPs
  let specs := (if heap.isEmpty then ["computes"] else heap) ++ ["decides"]
  let (ret, normal, returnExit) := firstResult p name bls sets source
  let setsT := sets.map fun l => (l.name, l.ty.toSTy)
  let recArgs (target : Option String) (q : Pos) (as : List SExpr) : List SExpr × List SExpr :=
    let h := target.getD g
    match ctx.sig? h with
    | some s =>
      let tys := if h == g then pls.map (·.ty) else s.params.map (·.subst ((instances.lookup h).getD []))
      let named := as.any fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
      if s.named.isEmpty && !named && as.length == tys.length then ([], as) else
      let n := s!"$recursiveArgs{q.line}_{q.col}"
      let types := ((instances.lookup h).getD []).map fun (n, t) =>
        SExpr.decl q n (some t.toSTy) false (.tuple q [])
      ([.decl q n (some (.tup (tys.map Ty.toSTy))) false
          (.app q (.ident q "$callArgs") [.ident q h, .block q as, .block q types] false)],
        tys.zipIdx.map fun (_, j) => .app q (.ident q n) [.int q (j : Int)] false)
    | none => ([], as)
  let extraFns ← members.mapM fun
    | .app _ (.ident _ "$member") [.ident _ h, .block _ hps, .block _ hcls, .decl _ _ _ _ htail] false => do
      let some sig := ctx.sig? h | throw s!"internal: no signature for {h} (#283)"
      let σ := (instances.lookup h).getD []
      let aliases := σ.map fun (n, t) => (Choice.memberTypeName h n, t.toSTy)
      let hcls := hcls.map (Refine.substTypes aliases)
      let htail := Refine.substTypes aliases htail
      let hparams : List SParam ← (hps.zip (sig.params.map (·.subst σ))).mapM fun
        | (.ident _ n, t) => pure { name := n, ty := t.toSTy }
        | _ => throw "internal: a $member parameter (#283)"
      let body := Choice.firstBody (nameOf h) p b bty hcls htail rest binds setsT capArgs (some vty.toSTy) nameOf
        (fun target => recArgs (some (target.getD h))) (if source.isSome then some normal else none)
      pure (STop.fn p (nameOf h) (hparams ++ capPs ++ typeParams) tps specs ret
        (pruneConstructHints ctx (nameOf h) body))
    | _ => throw "internal: a $member (#283)"
  return { key, pos := p, name, returnExit, sourceContext := sourceContextOf ctx, inlineScopes := ctx.inlineScopes, liftTag := ctx.liftTag,
           params := params ++ typeParams, tparams := tps, specs, ret,
           body := pruneConstructHints ctx name
             (Choice.firstBody name p b bty cls tail rest binds setsT capArgs (some vty.toSTy) nameOf recArgs
               (if source.isSome then some normal else none)),
           binds, sets := sets.map (·.name), args := pnames.map (SExpr.ident p ·) ++ caps.map (fun l => .ident p l.name) ++ typeArgs,
           varBinds := (bls.filter (·.mutable)).map (·.name), extraFns }

/-- (#335) The key of a continuation: where the composed choice is, its
    binding, and the consumer's names the clauses after it use (in a method,
    once its members are `Self`'s, as in the function), as `firstKey`. -/
def contKey (ctx : Ctx) (p : Pos) (b : String) (rest : List SExpr) : String :=
  let rest := match ctx.selfClass with
    | some c => rest.map (selfQualify ctx c)
    | none => rest
  -- (with their types: a `for`'s body copied once per alternative of a
  -- choice has the same place, with names of other types)
  let caps := (Choice.namesUsed (.block p rest)).eraseDups.filterMap fun n =>
    (ctx.lookup n).map fun l => s!"{n}:{reprStr l.ty}"
  -- A type used only by a written annotation has no captured value. Its
  -- instance still distinguishes helpers made at a shared source position.
  let written := ctx.types.tvars.filterMap fun (n, t) =>
    if writesTps [n] (.block p rest) then some s!"{n}:{reprStr t}" else none
  let typed := if written.isEmpty then "" else "_types:" ++ String.intercalate "," written
  -- (and the places of the clauses after it: the same choice, inside an
  -- alternative of another one with a continuation, has the call of that
  -- one after it in the next elaboration, which may use the same names)
  let places := rest.map fun c => s!"{c.pos.line}.{c.pos.col}"
  s!"k{p.line}_{p.col}_{p.file}_{b}_{String.intercalate "," caps}_{String.intercalate "," places}{typed}{ctx.liftTag}{reprStr ctx.inlineScopes}{sourceContextKey ctx}"

/-- (#335) The function of its own that the clauses after a composed choice
    (#296) are compiled as, where the first success is taken and those
    clauses (`rest`) have another such choice: called from each alternative
    with its value (`b`) and the consumer's names `rest` uses (from `ctx`,
    before the choice), it gives at the first success of `rest` the names
    they bind and the final values of the `var`s they set (their types from
    `c2`, after `rest`; `fxB`, the effects). So `rest` is compiled once, not
    once per alternative, which doubled the code with each such choice. Or
    why not, and the clauses are copied, as before. -/
def contLiftOf (ctx c2 : Ctx) (p : Pos) (b : String) (alts rest : List SExpr)
    (fxB : List (String × Pos × Option String)) : Except String Choice.FirstLift := do
  let written := SExpr.block p rest
  -- (the alternatives' names too: their types fix the binding's)
  let key := contKey ctx p b (alts ++ rest) ++ firstReturnKey ctx rest
  let σt := ctx.types.tvars.map fun (n, t) => (n, t.toSTy)
  let rest := rest.map (Refine.substTypes σt)
  -- (in a method: the members of `Self` the clauses name bare, as members
  -- of `Self`, which the function takes as a parameter, as #279's do)
  let rest ← match ctx.selfClass with
    | some c =>
      pure (rest.map (selfQualify ctx c))
    | none => pure rest
  -- (a `return`, or a `break` that leaves them, would leave the function)
  let source ← if firstReturns rest then
      some <$> (resolveTy ctx.types p (firstReturnType ctx)).run' { env := ctx.types }
    else pure none
  if (Refine.findPart (fun | .brk _ => true | _ => false) true (.block p rest)).isSome then throw "a break"
  let caps : List Local := (Choice.namesUsed (.block p rest)).eraseDups.filterMap ctx.lookup
  let setNames := Choice.setsIn (.block p rest)
  let sets := caps.filter fun l => l.mutable && setNames.contains l.name
  let binds := (b :: Choice.boundIn rest).eraseDups
  let bls ← binds.mapM fun n => match c2.lookup n with
    | some l => pure l
    | none => throw s!"internal: name {n}"
  let some bl := bls.head? | throw "internal: no binding"
  if bl.mutable then throw "a var binding"
  let (tps, typeParams, typeArgs) ← contTypes ctx p ((bl :: caps).map (·.ty)) (bls.map (·.ty) ++ source.toList) written
  let name := s!"$cont{p.line}_{p.col}_{key.hash}" ++ (if p.file.isEmpty then "" else s!"_{p.file}")
  -- (its effects the function's own: its body is that function's code,
  -- and it may call what is asked for only in the next elaboration, a
  -- `$first…` or `$refine…`, whose effects this one cannot see)
  let heap := ["reads", "writes", "allocates"].filter fun k => ctx.fnFx.contains k || fxB.any (·.1 == k)
  let (ret, tup, returnExit) := firstResult p name bls sets source
  -- (the `var`s it sets, copied from parameters named `m$in`, and given back)
  let copies := sets.map fun l => SExpr.decl p l.name (some l.ty.toSTy) true (.ident p s!"{l.name}$in")
  let params : List SParam := { name := b, ty := bl.ty.toSTy } ::
    caps.map fun l => { name := if sets.any (·.name == l.name) then s!"{l.name}$in" else l.name, ty := l.ty.toSTy }
  -- (`$firstP`: the clauses are lifted already, the consumer's, which lifting
  -- again would bind twice, as for #275's functions)
  return { key, pos := p, name, returnExit, sourceContext := sourceContextOf ctx, inlineScopes := ctx.inlineScopes, liftTag := ctx.liftTag,
           params := params ++ typeParams, tparams := tps,
           specs := (if heap.isEmpty then ["computes"] else heap) ++ ["decides"],
           ret,
           body := pruneConstructHints ctx name
             (.block p (copies ++ [.app p (.ident p "$firstP") [.block p (rest ++ [tup])] false])),
           binds, sets := sets.map (·.name),
           args := SExpr.ident p b :: caps.map (fun l => SExpr.ident p l.name) ++ typeArgs,
           varBinds := (bls.filter (·.mutable)).map (·.name) }

/-- The return slot is written by a moved consumer's source return. Its
    self-assignment is metadata for capture/write analysis, not executed. -/
def forReturnBody? : SExpr → Bool
  | .app _ (.ident _ f) _ false => f == "$forReturns" || f == "$forReturnBody"
  | _ => false

/-- Restore source exits for the current filter, while a body's own
    marker restores only its return target at actual body entry. -/
def forClauseExitScope (body inner : SExpr) : SExpr :=
  match body with
  | .app p (.ident _ f) [.block _ [metadata, breaking], mode, _] false =>
    if f == "$forReturns" || f == "$forReturnBody" then
      .app p (.ident p "$forClauseExits") [metadata, breaking, mode, inner] false
    else inner
  | .app p (.ident _ f) [metadata, mode, _] false =>
    if f == "$forReturns" || f == "$forReturnBody" then
      .app p (.ident p "$forReturnBody") [metadata, mode, inner] false
    else inner
  | _ => inner

def forStageBodyAs (body inner : SExpr) : SExpr :=
  match body with
  | .app p f@(.ident _ n) [metadata, mode, _] false =>
    if n == "$forReturns" || n == "$forReturnBody" then .app p f [metadata, mode, inner] false else inner
  | _ => inner

/-- Keep source breaks aimed at their original loop after adding the
    producer's private abort loop. Its own outcome abort is left alone. -/
partial def forwardForBreaks (abort escaped : Nat) : Expr → Expr
  | e@(.loop _) => e
  | e@(.ite (.prim .query [.local j]) yes (.seq .brk (.prim .userErr []))) =>
    if j == abort then e else
      .ite (.prim .query [.local j]) (forwardForBreaks abort escaped yes)
        (forwardForBreaks abort escaped (.seq .brk (.prim .userErr [])))
  | e@(.seq (.assign j (.lit (.logic false))) (.seq .brk (.prim .userErr []))) =>
    if j == abort then e else .seq (.assign escaped (.lit (.logic true))) e
  | .brk => .seq (.assign escaped (.lit (.logic true))) .brk
  | .assign i e => .assign i (forwardForBreaks abort escaped e)
  | .seq a b => .seq (forwardForBreaks abort escaped a) (forwardForBreaks abort escaped b)
  | .prim p es => .prim p (es.map (forwardForBreaks abort escaped))
  | .heap p es => .heap p (es.map (forwardForBreaks abort escaped))
  | .call f es => .call f (es.map (forwardForBreaks abort escaped))
  | .ite c t e => .ite (forwardForBreaks abort escaped c) (forwardForBreaks abort escaped t) (forwardForBreaks abort escaped e)
  | .forE i a f b => .forE i (forwardForBreaks abort escaped a) (forwardForBreaks abort escaped f) (forwardForBreaks abort escaped b)
  | .ret e => .ret (forwardForBreaks abort escaped e)
  | .print e => .print (forwardForBreaks abort escaped e)
  | e => e

/-- Whether a `for` body can move into a continuation. Source returns
    need an explicit outcome; breaks must stay inside the body's loops.
    The enclosing function may suspend; the moved code must remain
    immediate. Discovery also checks typed calls and pending cast lifts. -/
partial def forBodySafe (ctx : Ctx) (body : SExpr) : Bool :=
  let returns := forReturnBody? body
  -- Prepared consumers keep lazy producer templates (including groups and
  -- generic/default argument bindings) inside the body. Their ownership is
  -- checked when that consumer elaborates; they do not escape the helper.
  let safeMarkers := ["$sourceSuper", "$methodMiss", "$methodCast", "$methodCase", "$methodType", "$methodParams", "$inlineScope", "$inlineScopeEnd", "$inline", "$choice", "$excl", "$alt", "$firstP", "$first", "$each", "$noLift", "$fxOf",
    "$forReturns", "$forReturnBody", "$forClauseExits", "$defer", "$loop", "$rec", "$recTo", "$group", "$member", "$returnTail",
    "$tparams", "$params", "$defaults", "$paramDefault", "$freeNames", "$declNames", "$callArgs"]
  let rec blocked (e : SExpr) : Bool :=
    match e with
    -- Starting a task is immediate. elabSpawn checks its arguments in the
    -- caller and the waiting callee in its own suspension context.
    | .app _ (.ident _ "$spawn") _ false => false
    | e => (match e with
      | .ret .. => !returns
      | .app _ (.ident _ f) _ _ =>
        (f.startsWith "$" && !safeMarkers.contains f) || f == "Sleep" ||
          ((ctx.sig? f).map fun s => s.suspends || s.fx.contains "no_rollback").getD false
      | _ => false) || e.children.any blocked
  !(Refine.findPart (fun | .brk _ => true | _ => false) true body).isSome && !blocked body

/-- A shared for continuation runs inside a filter, so cannot suspend.
    Method/function-value calls need their typed signatures; a cast still
    being discovered can hide its suspension behind a placeholder. -/
def forContWaits (ctx : Ctx) (before after : ESt) (code : List Expr) : Bool :=
  ctx.suspends && (before.pendingSuspendingCasts != after.pendingSuspendingCasts ||
    before.pendingWaitingCasts != after.pendingWaitingCasts ||
    code.any (Suspend.hasSusp fun f => ctx.sigs.any fun s => s.idx == f && s.suspends))

/-- An admitted continuation rediscovers its local/frame metadata in its
    own helper. Its heap effects still belong to the enclosing source. -/
def restoreForContTrial (saved : ESt) : EM Unit := do
  let fx := (← get).fx
  set { saved with fx }

/-- (#335, phase 2) The continuation of a composed choice in a `for`: a
    function that runs the clauses after it (`rest`) and the body, failing
    where their first filter fails (`$forFirst`), and gives the values (and
    the final values of the `var`s they set), called from each alternative's
    own `for`. Its binding's type `bty`, the values' type `vty`. Or why not,
    and the clauses are copied, as before. -/
def contForLiftOf (ctx : Ctx) (p : Pos) (b : String) (bty vty : Ty) (alts rest : List SExpr) (body : SExpr) (outcome : Bool := false) :
    Except String Choice.FirstLift := do
  let written := SExpr.block p (rest ++ [body])
  let key := (if outcome then "fo" else "f") ++ contKey ctx p b (alts ++ rest ++ [body])
  let σt := ctx.types.tvars.map fun (n, t) => (n, t.toSTy)
  let rest := rest.map (Refine.substTypes σt)
  let body := Refine.substTypes σt body
  let (rest, body) ← match ctx.selfClass with
    | some c =>
      pure (rest.map (selfQualify ctx c), selfQualify ctx c body)
    | none => pure (rest, body)
  if !forReturnBody? body &&
      (Refine.findPart (fun | .ret .. => true | _ => false) false written).isSome then throw "a return"
  let body := match body with
    | .app q (.ident _ "$forReturns") args false => .app q (.ident q "$forReturnBody") args false
    | b => b
  let breaks := match body with
    | .app _ (.ident _ "$forReturnBody") [.block _ [_, .set _ (.ident _ _) none _], _, _] false => true
    | _ => false
  if !breaks && (Refine.findPart Refine.isBreak true (.block p rest)).isSome then throw "a break"
  let caps : List Local := (Choice.namesUsed (.block p (rest ++ [body]))).eraseDups.filterMap ctx.lookup
  let setNames := Choice.setsIn (.block p (rest ++ [body]))
  let sets := caps.filter fun l => l.mutable && setNames.contains l.name
  let (tps, typeParams, typeArgs) ← contTypes ctx p (bty :: caps.map (·.ty)) [vty] written
  let name := s!"$contf{p.line}_{p.col}_{key.hash}" ++ (if p.file.isEmpty then "" else s!"_{p.file}")
  let heap := ["reads", "writes", "allocates"].filter fun k => ctx.fnFx.contains k
  let copies := sets.map fun l => SExpr.decl p l.name (some l.ty.toSTy) true (.ident p s!"{l.name}$in")
  let params : List SParam := { name := b, ty := bty.toSTy } ::
    caps.map fun l => { name := if sets.any (·.name == l.name) then s!"{l.name}$in" else l.name, ty := l.ty.toSTy }
  let vals := s!"{b}$vals"
  let valueTy : STy := if outcome then .opt (.arr vty.toSTy) else .arr vty.toSTy
  let failure : SExpr := if sets.isEmpty then .ident p "false" else
    .tuple p (.ident p "false" :: sets.map fun l => SExpr.ident p l.name)
  let ffirst : SExpr := if outcome then
      .app p (.ident p "$forFirstOutcome") [.block p rest, body, failure] false
    else .app p (.ident p "$forFirst") [.block p rest, body] false
  let ffirst := match body with
    | .app q (.ident _ "$forReturnBody") [.block _ [metadata, breaking], mode, _] false =>
      .app q (.ident q "$forClauseExits") [metadata, breaking, mode, ffirst] false
    | .app q (.ident _ "$forReturnBody") [metadata, mode, _] false =>
      -- Clauses and body leave the same source function. A clause return
      -- succeeds with the packet, committing this filter's copy-outs.
      .app q (.ident q "$forReturnBody") [metadata, mode, ffirst] false
    | _ => ffirst
  let ret : STy := if sets.isEmpty then valueTy else .tup (valueTy :: sets.map (·.ty.toSTy))
  let bodyE : SExpr := if sets.isEmpty then .block p (copies ++ [ffirst]) else
    .block p (copies ++ [.decl p vals none false ffirst, .tuple p (.ident p vals :: sets.map fun l => SExpr.ident p l.name)])
  return { key, pos := p, name, sourceContext := sourceContextOf ctx, inlineScopes := ctx.inlineScopes, liftTag := ctx.liftTag,
           params := params ++ typeParams, tparams := tps,
           specs := (if heap.isEmpty then ["computes"] else heap) ++ ["decides"],
           ret, body := pruneConstructHints ctx name bodyE, binds := [], sets := sets.map (·.name),
           args := SExpr.ident p b :: caps.map (fun l => SExpr.ident p l.name) ++ typeArgs }

/-- The resume interface keeps every caller/frame type argument. A result
    alone can erase equations needed by borrowed frame-reference arguments. -/
def forStagePlanOf (ctx : Ctx) (p : Pos) (key : String) (clauses : List SExpr)
    (body : SExpr) (vty : Ty) (outcome : Bool) (required : List String := [])
    (sourceSuspends : Bool := false) : Except String Choice.FirstLift := do
  let qualify := match ctx.selfClass with | some c => selfQualify ctx c | none => id
  let clauses := clauses.map qualify
  let body := qualify body
  let written := SExpr.block p (clauses ++ [body] ++ required.map (SExpr.ident p ·))
  let used := Choice.namesUsed written
  let caps := used.eraseDups.filterMap ctx.lookup
  let setNames := Choice.setsIn written
  let sets := caps.filter fun l => l.mutable && setNames.contains l.name
  let inputs := caps.flatMap fun l => l.storage.toList.flatMap (·.args)
  let (tps, _, _) ← contTypes ctx p inputs (vty :: sets.map (·.ty)) (.tuple p [])
  let base := s!"$forStage{p.line}_{p.col}_{key.hash}"
  let method := base ++ "$resume"
  let specs := (if ctx.fnFx.isEmpty then ["computes"] else ctx.fnFx) ++ ["suspends"]
  let copies := sets.map fun l => (l.name, l.ty.toSTy)
  let borrowed := caps.filterMap fun l => if l.storage.isSome then some l.name else none
  let plan : Choice.ForStagePlan := {
    key, pos := p, base, method, tparams := tps,
    value := vty.toSTy, copies, borrowed, specs, outcome, sourceSuspends }
  let valueTy := if outcome then STy.opt (.arr plan.value) else .arr plan.value
  let ret := if copies.isEmpty then valueTy else .tup (valueTy :: copies.map (·.2))
  let cls := STop.classDef p base tps [] [] true [] []
    [.fn p method [] [] ("$abstract" :: specs) ret (.tuple p [])]
  return {
    stageOnly := true, stagePlan := some plan, key, pos := p, name := base,
    params := [], specs := ["computes"], ret := .name "void", body := .tuple p [],
    binds := [], sets := [], args := [], extraFns := [cls] }

/-- Storage and the ordered root view are part of generated-code identity. -/
def forStageCaptureKey (ctx : Ctx) (args : List Ty) (caps : List Local) : String :=
  let origins := caps.map fun l => s!"{l.name}:{l.mutable}:" ++ match l.storage with
    | none => "local"
    | some s => s!"{s.frame}:{s.name}:{reprStr s.args}"
  s!"{ctx.frameName}:{ctx.refineScope}:{ctx.inChoice}:{ctx.inRepeat}:" ++
    reprStr args ++ String.intercalate ";" origins

def forStageView (base : String) (args : List STy) : STy :=
  if args.isEmpty then .name base else .app base args

def forStageCopyMetadata (p : Pos) (names : List String) : SExpr :=
  .block p (names.map fun n => .set p (.ident p n) none (.ident p n))

def forStageCopyNames (ids : List SExpr) : List String :=
  ids.filterMap fun
    | .set _ (.ident _ n) none _ => some n
    | .ident _ n => some n
    | _ => none

/-- A shared prefix still runs in the alternative's current filter. Its
    singleton environment is resumed only from that alternative's body. -/
def forStageInvoke (p : Pos) (prepare : Choice.FirstLift) (borrowed : List String)
    (body : SExpr) : List SExpr × SExpr :=
  let payload := prepare.name ++ "$ready"
  let packet := payload ++ "$packet"
  let call := SExpr.app p (.ident p prepare.name) prepare.args true
  let get (j : Nat) := SExpr.app p (.ident p packet) [.int p (j : Int)] false
  let clauses := if prepare.sets.isEmpty then [.decl p payload none false call] else
    .decl p packet none false call ::
      (prepare.sets.zipIdx.map fun (n, j) => .set p (.ident p n) none
        (.app p (.ident p "$refineCopyOut") [get (j + 1)] false)) ++
      [.decl p payload none false (get 0)]
  let resume := SExpr.app p (.ident p "$forResumeValues")
    [.ident p payload, forStageCopyMetadata p prepare.sets,
      .block p (borrowed.map (SExpr.ident p ·))] false
  (clauses, forStageBodyAs body resume)

/-- Give the immediate prefix an actual function boundary. A source exit
    returns its normal packet even from nested source loops; ordinary prefix
    failure still fails the call in the caller's original filter. -/
def forStagePrefixOf (ctx : Ctx) (plan : Choice.ForStagePlan) (args : List Ty) (p : Pos)
    (clauses : List SExpr) (body : SExpr) (flat : Bool := false)
    (copyNames : List String := plan.copies.map (·.1))
    (borrowNames : List String := plan.borrowed) : Except String Choice.FirstLift := do
  let qualify := match ctx.selfClass with | some c => selfQualify ctx c | none => id
  -- Default annotations use private lexical aliases. Resolve them before
  -- the prefix moves into a function with only its own type parameters.
  let σt := ctx.types.tvars.map fun (n, t) => (n, t.toSTy)
  let clauses := clauses.map fun e => Refine.substTypes σt (qualify e)
  let body := Refine.substTypes σt (qualify body)
  let written := SExpr.block p (clauses ++ [body] ++ (copyNames ++ borrowNames).map (SExpr.ident p ·))
  let caps := (Choice.namesUsed written).eraseDups.filterMap ctx.lookup
  let key := s!"prefix{flat}" ++ plan.key ++ contKey ctx p "$prepare" [written] ++ forStageCaptureKey ctx args caps
  let name := s!"{plan.base}$prepare{key.hash}"
  let (tps, more, witnesses) ← contTypes ctx p (caps.map (·.ty)) args written
  let params := caps.map fun l => ({ name := if l.mutable then l.name ++ "$in" else l.name, ty := l.ty.toSTy } : SParam)
  let init := caps.filterMap fun l => if !l.mutable then none else some
    (SExpr.decl p l.name (some l.ty.toSTy) true
      (.app p (.ident p "$refineCopyIn") [.ident p (l.name ++ "$in")] false))
  let view := forStageView plan.base (args.map Ty.toSTy)
  let stage := SExpr.app p (.ident p "$forStage")
    [.str p [.text plan.base], .decl p "$stageView" (some view) false (.tuple p []),
      forStageCopyMetadata p copyNames, .block p (borrowNames.map (SExpr.ident p ·)),
      .ident p "true", .ident p (if flat then "true" else "false"), .block p clauses, body] false
  let stage := forClauseExitScope body stage
  let value := s!"{name}$value"
  let code := if plan.copies.isEmpty then stage else SExpr.block p
    [.decl p value none false stage, .tuple p (.ident p value :: copyNames.map (SExpr.ident p ·))]
  let valueTy := if plan.outcome then STy.opt (.arr view) else .arr view
  let σ := (plan.tparams.map (·.name)).zip (args.map Ty.toSTy)
  let ret := if plan.copies.isEmpty then valueTy else .tup (valueTy :: plan.copies.map (fun (_, t) => t.substNames σ))
  let storage := caps.filterMap fun l => l.storage.map fun s =>
    (if l.mutable then l.name ++ "$in" else l.name,
      ({ frame := s.frame, name := s.name, args := s.args.map Ty.toSTy } : Choice.ResumeStorage))
  let info : Choice.ForResume := {
    name, storage, inlineScopes := ctx.inlineScopes, liftTag := ctx.liftTag,
    inRepeat := ctx.inRepeat, inChoice := ctx.inChoice, sourceContext := sourceContextOf ctx }
  return {
    key, pos := p, name, params := params ++ more, tparams := tps,
    specs := plan.specs.filter (· != "suspends") ++ ["decides"], ret,
    body := pruneConstructHints ctx name (.block p (init ++ [code])),
    binds := [], sets := copyNames,
    args := caps.map (fun l => .ident p l.name) ++ witnesses.map (fun
      | .app q (.ident _ "$witness") [.ident _ n] false =>
        .app q (.ident q "$stageWitness") [.decl q n (some (.name n)) false (.tuple q [])] false
      | e => e), resumes := [info] }

/-- Close over the remaining generators/body without executing either.
    A class retains existential bindings and supplies a typed resume method;
    mutable local aliases still name their original source-frame storage. -/
def forStageEnvOf (ctx : Ctx) (plan : Choice.ForStagePlan) (p : Pos)
    (clauses : List SExpr) (body : SExpr) : Except String (Choice.FirstLift × SExpr × Ty) := do
  let qualify := match ctx.selfClass with | some c => selfQualify ctx c | none => id
  let clauses := clauses.map qualify
  let body := qualify body
  let written := SExpr.block p (clauses ++ [body] ++ (ctx.forStageCopies ++ ctx.forStageBorrows).map (SExpr.ident p ·))
  let caps := (Choice.namesUsed written).eraseDups.filterMap ctx.lookup
  let key := s!"env{ctx.forStageFlat}" ++ plan.key ++ contKey ctx p "$resume" [written] ++ forStageCaptureKey ctx ctx.forStageArgs caps
  let name := s!"{plan.base}$env{key.hash}"
  let args := ctx.forStageArgs
  let (tps, _, _) ← contTypes ctx p (args ++ caps.map (·.ty) ++
    caps.flatMap (fun l => l.storage.toList.flatMap (·.args))) [] written
  let σ := (plan.tparams.map (·.name)).zip (args.map Ty.toSTy) ++
    ctx.types.tvars.map fun (n, t) => (n, t.toSTy)
  let rename := Choice.renameE [("Self", "$sourceSelf")]
  let clauses := clauses.map fun e => rename (Refine.substTypes σ e)
  let body := rename (Refine.substTypes σ body)
  let body := match body with
    | .app p (.ident _ "$forReturns") args false => .app p (.ident p "$forReturnBody") args false
    | b => b
  let localName (n : String) := if n == "Self" then "$sourceSelf" else n
  let fields := caps.zipIdx.map fun (l, j) => (s!"$capture{j}", l.ty.toSTy, none, false)
  let borrowed (l : Local) := l.storage.filter fun s =>
    !(ctx.sig? s.frame).any (!·.suspends)
  let init := caps.zipIdx.flatMap fun (l, j) =>
    let value := SExpr.app p (.ident p "$forEnvCapture")
      [.member p (.ident p "Self") s!"$capture{j}"] false
    if (borrowed l).isSome then
      let saved := s!"$captureInit{j}"
      [SExpr.decl p saved (some l.ty.toSTy) false value,
        .decl p (localName l.name) (some l.ty.toSTy) l.mutable
          (.app p (.ident p "$forEnvInit") [.ident p saved] false)]
    else [SExpr.decl p (localName l.name) (some l.ty.toSTy) l.mutable value]
  let copies := ctx.forStageCopies.map fun n => SExpr.ident p (localName n)
  let vals := s!"{name}$values"
  let failed : SExpr := if copies.isEmpty then .ident p "false" else .tuple p (.ident p "false" :: copies)
  let run := if plan.outcome then
      SExpr.app p (.ident p "$forFirstOutcome") [.block p clauses, body, failed] false
    else SExpr.app p (.ident p "$forFirst") [.block p clauses, body] false
  let run := forClauseExitScope body run
  let run := if ctx.forStageFlat then SExpr.app p (.ident p "$forStageFlatten") [run] false else run
  let code := if copies.isEmpty then run else .block p
    [.decl p vals none false run, .tuple p (.ident p vals :: copies)]
  let valueTy := if plan.outcome then STy.opt (.arr (plan.value.substNames σ)) else .arr (plan.value.substNames σ)
  let ret := if copies.isEmpty then valueTy else
    .tup (valueTy :: plan.copies.map (fun (_, t) => t.substNames σ))
  let method := STop.fn p plan.method [] [] ("override" :: plan.specs) ret
    (pruneConstructHints ctx s!"{name}.{plan.method}" (.block p (init ++ [code])))
  let storage := caps.filterMap fun l => (borrowed l).map fun s =>
    (localName l.name, ({ frame := s.frame, name := s.name, args := s.args.map Ty.toSTy } : Choice.ResumeStorage))
  let resumeInfo : Choice.ForResume := {
    name := s!"{name}.{plan.method}", storage,
    inlineScopes := ctx.inlineScopes, liftTag := ctx.liftTag, sourceContext := sourceContextOf ctx }
  let cls := STop.classDef p name tps [] [forStageView plan.base (args.map Ty.toSTy)] false fields [] [method]
  let req : Choice.FirstLift := {
    stageOnly := true, resumes := [resumeInfo], key, pos := p, name,
    params := [], specs := ["computes"], ret := .name "void", body := .tuple p [],
    binds := [], sets := [], args := [], extraFns := [cls] }
  let obj := SExpr.construct p name (tps.map fun tp => .name tp.name)
    (caps.zipIdx.map fun (l, j) => .decl p s!"$capture{j}" none false (.ident p l.name))
  return (req, obj, .struct plan.base args)

/-- A failed body is unwrapped in an iteration body. Inside an outcome
    producer, stop its private loop instead of failing the filter. -/
def forOutcomeValues (ctx : Ctx) (p : Pos) (r : R) : EM R := do
  let .opt (.arr t) := r.ty | eerr p "internal: expected a for outcome"
  -- A waiting method returns before its outcome can be queried. Only the
  -- saved option belongs in a condition; the call stays outside it.
  let (before, input) ← if ctx.suspends && Suspend.hasSusp
      (fun f => ctx.sigs.any fun s => s.idx == f && s.suspends) r.e then do
      let slot ← fresh r.ty
      pure ([Expr.assign slot r.e], Expr.local slot)
    else pure ([], r.e)
  let value := Expr.prim .query [input]
  if let some flag := ctx.forOutcomeSlot then
    let slot ← fresh (.arr t)
    return ⟨before.foldr Expr.seq (.ite (.assign slot value) (.local slot)
      (.seq (.assign flag (.lit (.logic false))) (.seq .brk (.prim .userErr [])))), .arr t⟩
  return ⟨before.foldr Expr.seq value, .arr t⟩

/-- `for`: clauses are generators, bindings and filters; each generator opens
    a nested `forE`, and nested results are flattened (cartesian product,
    leftmost outermost). The clauses are a failure context; the body is not.
    Defined before the mutual block, with the functions of the block it
    calls as arguments (named as they are), so that it is a command of its
    own, with its own heartbeats (#325); `elabFor` in the block passes them. -/
partial def elabForWith (elabAlts : Ctx → Pos → Choice.Binding → EM (Ty × List Expr))
    (elabBranchAlts : Ctx → Pos → SExpr → Option STy → Option SExpr → EM (Option Expr × Ty × List Expr × Bool))
    (elabE : Ctx → SExpr → Option Ty → EM R) (elabInts : Ctx → Pos → List SExpr → EM (List Expr))
    (elabLoopGen : Ctx → Pos → List SExpr → EM LoopGen) (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx))
    (ctx : Ctx) (p : Pos) (clauses : List SExpr) (body : SExpr) (prepared : Bool := false)
    (firstDecides : Bool := false) (failure : Option SExpr := none) : EM R := do
  let stagePlan := ctx.forStage
  let stageArgs := ctx.forStageArgs
  let stageFlat := ctx.forStageFlat
  let stageCopies := ctx.forStageCopies
  let stageBorrows := ctx.forStageBorrows
  let ctx := { ctx with liftWhy := "", forStage := none, forStageArgs := [], forStageFlat := false, forStageCopies := [], forStageBorrows := [] }
  -- (a choice is a generator over its alternatives, #208; clauses lifted
  -- already, `prepared`, are not lifted again)
  let clauses := if prepared then clauses else
    Choice.prepare clauses (choiceValues ctx) (choiceField ctx) (fieldOrder := choiceOrder ctx) (keepExcl := true)
      (keepBranches := choiceHasCast ctx)
  -- (a call of a recursive function with several values, #235: a generator
  -- over the array of its values; at a written type, through a binding)
  let normGens (cs : List SExpr) : List SExpr := cs.flatMap fun c => match Choice.binding? c with
    | some { each := some (.app _ (.ident _ "$loop") _ false), .. } => [c]
    | some { pos := q, name := n, ty := none, each := some arr, .. } => [.gen q n none arr]
    | some { pos := q, name := n, ty := some t, each := some arr, .. } =>
      let tmp := s!"$e{q.line}_{q.col}"
      [.gen q tmp none arr, .decl q n (some t) false (.ident q tmp)]
    | _ => [c]
  let clauses := clauses.flatMap fun c => match Choice.binding? c with
    -- (one taken lazily, #246: the binding stays, a generator of its own)
    | some { each := some (.app _ (.ident _ "$loop") _ false), .. } => [c]
    | some { pos := q, name := n, ty := none, each := some arr, .. } => [.gen q n none arr]
    | some { pos := q, name := n, ty := some t, each := some arr, .. } =>
      let tmp := s!"$e{q.line}_{q.col}"
      [.gen q tmp none arr, .decl q n (some t) false (.ident q tmp)]
    | _ => [c]
  -- split into groups: [filters before the first generator], then (generator, filters)…
  let isBranch (c : SExpr) : Bool := (Choice.binding? c).any (·.branchy.isSome)
  let isGen : SExpr → Bool
    | .gen .. => true
    | .decl _ _ none false (.range ..) => true
    | c => !isBranch c && (Choice.binding? c).isSome
  -- (an exclusive choice's binding, #314: no generator, but paths)
  let isExcl : SExpr → Bool
    | .decl _ _ _ false (.app _ (.ident _ "$excl") _ false) => true
    | c => isBranch c
  -- (a composed choice whose alternatives have values or clauses of their
  -- own, #283, or an exclusive one: what a continuation saves copying, #335)
  let isCF (x : SExpr) : Bool := isExcl x || (match Choice.binding? x with
    | some { place := none, branchy := none, each := none, alts := xs, .. } => xs.any Choice.hasLiftable
    | _ => false)
  let pre := clauses.takeWhile (!isGen ·)
  let rest := clauses.dropWhile (!isGen ·)
  let rec groups : List SExpr → List (SExpr × List SExpr)
    | [] => []
    | g :: cs =>
      let fs := cs.takeWhile (!isGen ·)
      (g, fs) :: groups (cs.dropWhile (!isGen ·))
  let gs := groups rest
  -- A failable continuation body returns an explicit outcome. Its first
  -- filter still fails the call, so the caller retains that boundary.
  let bodyFail := (ctx.canFail && !firstDecides) || failure.isSome || forReturnBody? body
  let bodyCtx (c : Ctx) : Ctx := { c with
    canFail := bodyFail, inLoop := false, inRepeat := true, forBreakSlot := none, forBreakCapture := none,
    refineExits := { c.refineExits with brk := none },
    forExitPacket := failure.orElse fun _ => c.forExitPacket }
  -- elaborate the filters of one generator (in a failure context)
  let elabFilters (c : Ctx) (fs : List SExpr) : EM (Expr × Ctx) := do
    match fs with
    | [] => return (.lit (.logic true), c)
    | _ =>
      let (r, c') ← elabSeq { c with canFail := true, inTaking := true } fs none
      return (r.e, c')
  -- The ordinary composed/exclusive paths use the same handoff as a
  -- refining path. Probe a suffix once at its binding's common type;
  -- type-only probes recurse through these same shared suffixes.
  let stagedSuffix (c : Ctx) (q : Pos) (name : String) (bty : Ty)
      (alts rest : List SExpr) (bd : SExpr) (flat : Option Bool := none) :
      EM (Option (Choice.FirstLift × Choice.ForStagePlan × Ty × Bool)) := do
    let sourceFail := match bd with
      | .app _ (.ident _ f) [_, .ident _ mode, _] false =>
        if f == "$forReturns" || f == "$forReturnBody" then mode == "true" else bodyFail
      | _ => bodyFail
    if (stagePlan.isNone && (!c.suspends || sourceFail)) ||
        c.inCtor || c.inBlock || c.inDefer then return none
    checkNewLocal c q name
    let before ← get
    let slot ← fresh bty
    let bound := { c with locals := { name, slot, ty := bty, mutable := false } :: c.locals }
    let required := if stagePlan.isSome then stageBorrows else []
    let written := SExpr.block q (rest ++ [bd] ++ required.map (SExpr.ident q ·))
    let caps := (Choice.namesUsed written).eraseDups.filterMap bound.lookup
    let key := "stageOrdinary" ++ contKey bound q name (alts ++ rest ++ [bd]) ++
      forStageCaptureKey bound stageArgs caps
    let known := c.types.loopRequests.findSome? (fun l => l.stagePlan.filter (·.key == key))
    let value? ← if let some outer := stagePlan then do
        let subst := (outer.tparams.map (·.name)).zip (stageArgs.map Ty.toSTy)
        pure (some (← resolveTy c.types q (outer.value.substNames subst), true, before.fx, outer.sourceSuspends))
      else if let some plan := known then
        pure (some (← resolveTy c.types q plan.value, true, before.fx, plan.sourceSuspends))
      else tryCatch (do
        let r ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
          { bound with typeOnly := true } p rest bd (prepared := true) (firstDecides := true)
        let .arr value := r.ty | pure none
        let after ← get
        pure (some (value, forContWaits c before after [r.e], after.fx,
          before.pendingSourceSuspends != after.pendingSourceSuspends || c.sourceWaits r.e))) (fun _ => pure none)
    set before
    let some (value, waits, effects, sourceSuspends) := value? | return none
    if stagePlan.isNone && !waits && forBodySafe c bd then return none
    -- Refining lifts can infer their effects. Their initially empty fnFx
    -- is not an explicit computes restriction; retain the suffix's typed
    -- effects, as immediate continuations do, and expose them to a parent
    -- type-only probe as well.
    let allowed := heapFx.filter fun fx => c.fnFx.contains fx || effects.any (·.1 == fx) ||
      (stagePlan.orElse fun _ => known).any (·.specs.contains fx)
    let bound := { bound with fnFx := allowed }
    let request ← match forStagePlanOf bound q key rest bd value ((stagePlan.map (·.outcome)).getD bodyFail) required sourceSuspends with
      | .ok request => pure request
      | .error _ => return none
    let some plan := request.stagePlan | return none
    let args := plan.tparams.map fun tp =>
      (c.types.tvars.lookup tp.name).getD (.param tp.name (tp.constraint == "comparable"))
    let flatten := stagePlan.isSome && flat.getD stageFlat
    let prepare ← match forStagePrefixOf bound plan args q rest bd flatten with
      | .ok prepare => pure prepare
      | .error _ => return none
    let hasPlan := c.types.loopRequests.any (·.key == request.key)
    let hasPrefix := c.types.loopRequests.any (·.key == prepare.key)
    modify fun st => { st with
      fx := effects,
      pendingSourceSuspends := st.pendingSourceSuspends + (if sourceSuspends then 1 else 0) }
    noteFx q (heapFx.filter fun fx => (stagePlan.orElse fun _ => known).any (·.specs.contains fx))
      (some prepare.name)
    if !c.typeOnly then
      for req in (if hasPlan then [] else [request]) ++ (if hasPrefix then [] else [prepare]) do
        modify fun st => { st with loopFirst := st.loopFirst ++
          [{ g := "", pos := q, itemCode := .lit .void, argSet := none, lift := .ok req }] }
      modify fun st => { st with
        forStageUses := st.forStageUses + 1,
        pendingSuspendingCasts := st.pendingSuspendingCasts + (if c.suspends && (!hasPlan || !hasPrefix) then 1 else 0),
        pendingWaitingCasts := st.pendingWaitingCasts + (if c.suspends && (!hasPlan || !hasPrefix) then 1 else 0) }
    else
      -- A type-only parent must still see the wait hidden by this staged
      -- placeholder, including a function-value call in a nested for.
      modify fun st => { st with
        pendingSuspendingCasts := st.pendingSuspendingCasts + 1,
        pendingWaitingCasts := st.pendingWaitingCasts + 1 }
    return some (prepare, plan, value, !c.typeOnly && hasPlan && hasPrefix)
  let rec build (c : Ctx) (gs : List (SExpr × List SExpr)) (bd : SExpr)
      (stageHere : Bool := true) (flatOverride : Option Bool := none) : EM R := do
    if let some plan := stagePlan.filter (fun _ => stageHere) then
      let clauses := gs.flatMap fun (g, fs) => g :: fs
      let (req, obj, ty) ← match forStageEnvOf { c with forStageArgs := stageArgs, forStageFlat := flatOverride.getD stageFlat, forStageCopies := stageCopies, forStageBorrows := stageBorrows } plan p clauses bd with
        | .ok r => pure r
        | .error why => eerr p s!"cannot stage this for: {why} (#417)"
      let r ← if c.types.loopRequests.any (·.key == req.key) then do
          -- Only this synthetic environment allocation is an implementation
          -- effect. Its fields are local reads, evaluated before allocation.
          let fx := (← get).fx
          let r ← elabE c obj (some ty)
          let e ← coerce p r ty
          modify fun st => { st with fx }
          pure (⟨e, ty⟩ : R)
        else do
          modify fun st => { st with loopFirst := st.loopFirst ++
            [{ g := "", pos := p, itemCode := .lit .void, argSet := none, lift := .ok req }] }
          pure (⟨.prim .userErr [], ty⟩ : R)
      if gs.isEmpty then return r
      return ⟨.prim .mkArr [r.e], .arr r.ty⟩
    -- (#314) filters `fs` with an exclusive choice among them, then the
    -- groups `more`: its guards pick a path into a selector; each path's
    -- clauses up to its first generator (its guards again, which bind its
    -- names, its clauses, then the filters after the choice) go into this
    -- filter under the selector, so a failure there rolls back to this
    -- iteration's generator; each path's generators into the iteration's
    -- body, under it. The filter's code, the body's (an array of the
    -- values), and their type.
    let rec exclIter (c : Ctx) (fs : List SExpr) (more : List (SExpr × List SExpr))
        (bd : SExpr) (stageOverride : Option Bool := none) : EM (Expr × Expr × Ty) := do
      match fs.findIdx? isExcl with
      | none =>
        let (filt, c') ← elabFilters c fs
        let inner ← build c' more bd (flatOverride := stageOverride)
        match more with
        | [] => return (filt, .prim .mkArr [inner.e], inner.ty)
        | _ => match inner.ty with
          | .arr t => return (filt, inner.e, t)
          | _ => eerr p "internal: nested for"
      | some j =>
        let (codeA, cA) ← elabFilters c (fs.take j)
        let after := fs.drop (j + 1)
        let moreCl := more.flatMap fun (g', fs') => g' :: fs'
        -- A refining condition must remain with the branch. A safe body
        -- can run inside $forFirst with the suffix: its first segment
        -- still belongs to this filter, and later generators keep their
        -- effects even when empty. The option prevents failure of a
        -- selected branch from choosing the else branch instead.
        if let some b@{ branchy := some i, .. } := fs[j]?.bind Choice.binding? then
          let i := pruneMethodCases cA i
          let st ← get
          let (_, ty, _, refined) ← elabBranchAlts { cA with canFail := true, inTaking := true, typeOnly := true }
            b.pos i b.ty b.place
          restoreConstructProbe cA st
          if refined && stagePlan.isNone && forBodySafe cA bd then
            checkNewLocal cA b.pos b.name
            if cA.typeOnly then
              let slot ← fresh ty
              let cB := { cA with locals := { name := b.name, slot, ty, mutable := false } :: cA.locals }
              let (f, a, t) ← exclIter cB after more bd stageOverride
              return (.seq codeA f, a, t)
            let restCl := after ++ moreCl
            let key := (if bodyFail then "fo" else "f") ++ contKey cA b.pos b.name (i :: restCl ++ [bd])
            let req := cA.types.loopRequests.find? (·.key == key)
            let fits (l : Choice.FirstLift) : Bool :=
              cA.acceptsHelper l
            if req.isNone && (contForLiftOf cA b.pos b.name ty .void [i] restCl bd bodyFail).toOption.isSome then
              -- Elaborate the suffix once, in its source context. Otherwise
              -- an inner lift can retain an outer var's old name after the
              -- enclosing lift has renamed it for mutable copy-out.
              let st0 ← get
              let slot ← fresh ty
              let cB := { cA with locals := { name := b.name, slot, ty, mutable := false } :: cA.locals }
              let values ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
                cB p restCl bd (prepared := true) (firstDecides := true)
                  (failure := if bodyFail then some (.app p (.ident p "Err") [] false) else none)
              let .arr t := values.ty | eerr b.pos "internal: a refining for's suffix"
              if forContWaits cA st0 (← get) [values.e] then set st0 else
                match contForLiftOf cA b.pos b.name ty t [i] restCl bd bodyFail with
                | .ok lift =>
                  -- This body moves to an immediate helper. Its trial's
                  -- source-frame locals/cast requests do not exist in the
                  -- final suspending caller; discover them in the helper.
                  if cA.suspends then restoreForContTrial st0
                  modify fun st => { st with loopFirst := st.loopFirst ++
                    [{ g := "", pos := b.pos, itemCode := .lit .void, argSet := none, lift := .ok lift }] }
                  return (codeA, .prim .userErr [], t)
                | .error why => eerr b.pos s!"cannot share the refining for's suffix: {why} (#417)"
            if let some l := req.filter fits then
              let kv := s!"$refineFor{b.pos.line}_{b.pos.col}{b.name}v"
              let kt := kv ++ "t"
              let elem := kv ++ "e"
              let call := SExpr.app b.pos (.ident b.pos l.name) l.args true
              let callCl : List SExpr := if l.sets.isEmpty then [.decl b.pos kv none false call] else
                [.decl b.pos kt none false call] ++
                  l.sets.zipIdx.map (fun (n, j) => SExpr.set b.pos (.ident b.pos n) none
                    (.app b.pos (.ident b.pos kt) [.int b.pos ((j + 1 : Nat) : Int)] false)) ++
                  [.decl b.pos kv none false (.app b.pos (.ident b.pos kt) [.int b.pos 0] false)]
              let site := s!"$refineFor{b.pos.line}_{b.pos.col}{b.name}"
              let consume (arm : SExpr) : SExpr :=
                let cl := Choice.prepare [.decl b.pos b.name (some ty.toSTy) false arm]
                  (choiceValues cA) (choiceField cA) (site := site) (fieldOrder := choiceOrder cA)
                  (keepExcl := true) (keepBranches := choiceHasCast cA)
                let vals : SExpr := if bodyFail then
                  .app b.pos (.ident b.pos "$forOutcomeValues") [.ident b.pos kv] false
                  else .ident b.pos kv
                let clauses := .block b.pos (cl ++ callCl ++ [.gen b.pos elem none vals])
                .optionLit b.pos (if bodyFail then
                    .app b.pos (.ident b.pos "$forFirstOutcome")
                      [clauses, .ident b.pos elem, .app b.pos (.ident b.pos "Err") [] false] false
                  else .app b.pos (.ident b.pos "$forFirst") [clauses, .ident b.pos elem] false)
              let selected := Choice.consumeBranches i site consume
              let values ← elabE { cA with canFail := true, inTaking := true } (.query b.pos selected) none
              let arrTy := if bodyFail then match values.ty with | .opt t => t | t => t else values.ty
              let .arr t := arrTy | eerr b.pos "internal: a refining for's values"
              let slot ← fresh values.ty
              let value ← if bodyFail then forOutcomeValues cA b.pos ⟨.local slot, values.ty⟩ else pure ⟨.local slot, values.ty⟩
              return (.seq codeA (.assign slot values.e), value.e, t)
          -- A waiting body cannot move into a filter-bound continuation.
          -- Prepare only this filter's prefix, then dispatch its typed
          -- environment from the iteration body after the filter commits.
          let sourceFail := match bd with
            | .app _ (.ident _ f) [_, .ident _ mode, _] false =>
              if f == "$forReturns" || f == "$forReturnBody" then mode == "true" else bodyFail
            | _ => bodyFail
          if refined && (stagePlan.isSome || (ctx.suspends && !sourceFail)) &&
              !cA.inCtor && !cA.inBlock && !cA.inDefer then
            checkNewLocal cA b.pos b.name
            let restCl := after ++ moreCl
            if cA.typeOnly then
              let slot ← fresh ty
              let cB := { cA with locals := { name := b.name, slot, ty, mutable := false } :: cA.locals }
              let (f, a, t) ← exclIter cB after more bd stageOverride
              return (.seq codeA f, a, t)
            let rootCaptures := (Choice.namesUsed (.block p (i :: restCl ++ [bd]))).filterMap cA.lookup
            let key := "stage" ++ contKey cA b.pos b.name (i :: restCl ++ [bd]) ++
              forStageCaptureKey cA [] (rootCaptures.filter (·.storage.isSome))
            let plan? := stagePlan.orElse fun _ =>
              cA.types.loopRequests.findSome? (fun l => l.stagePlan.filter (·.key == key))
            if plan?.isNone then
              let saved ← get
              let slot ← fresh ty
              let cB := { cA with
                typeOnly := true, forStage := none,
                locals := { name := b.name, slot, ty, mutable := false } :: cA.locals }
              let values ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
                cB p restCl bd (prepared := true) (firstDecides := true)
              let .arr value := values.ty | eerr b.pos "internal: staged for result"
              let effects := (← get).fx
              let sourceSuspends := saved.pendingSourceSuspends != (← get).pendingSourceSuspends || cA.sourceWaits values.e
              set { saved with
                fx := effects,
                pendingSourceSuspends := saved.pendingSourceSuspends + (if sourceSuspends then 1 else 0) }
              let allowed := heapFx.filter fun k => cA.fnFx.contains k || effects.any (·.1 == k)
              let req ← match forStagePlanOf { cA with fnFx := allowed } b.pos key (i :: restCl) bd value bodyFail [] sourceSuspends with
                | .ok req => pure req
                | .error why => eerr b.pos s!"cannot stage this refining for: {why} (#417)"
              modify fun st => { st with
                loopFirst := st.loopFirst ++ [{ g := "", pos := b.pos, itemCode := .lit .void, argSet := none, lift := .ok req }],
                pendingSuspendingCasts := st.pendingSuspendingCasts + 1,
                pendingWaitingCasts := st.pendingWaitingCasts + 1,
                forStageUses := st.forStageUses + 1 }
              return (codeA, .prim .userErr [], value)
            let some plan := plan? | eerr b.pos "internal: staged for plan"
            if plan.sourceSuspends then
              modify fun st => { st with pendingSourceSuspends := st.pendingSourceSuspends + 1 }
            noteFx b.pos (heapFx.filter plan.specs.contains)
            let site := s!"{plan.base}$selected"
            let rootArgs := if stagePlan.isSome then stageArgs else
              plan.tparams.map fun tp => (cA.types.tvars.lookup tp.name).getD (.param tp.name (tp.constraint == "comparable"))
            let copyNames := if stagePlan.isSome then stageCopies else plan.copies.map (·.1)
            let borrowNames := if stagePlan.isSome then stageBorrows else plan.borrowed
            let suffixCtx := { cA with
              fnFx := heapFx.filter (fun k => cA.fnFx.contains k || plan.specs.contains k),
              locals := { name := b.name, slot := 0, ty, mutable := false } :: cA.locals }
            let viewSub := (plan.tparams.map (·.name)).zip (rootArgs.map Ty.toSTy)
            let resultTy ← resolveTy cA.types b.pos (plan.value.substNames viewSub)
            let tailKey := "tail" ++ contKey suffixCtx b.pos b.name (restCl ++ [bd]) ++ reprStr resultTy ++
              forStageCaptureKey cA rootArgs (borrowNames.filterMap cA.lookup)
            let nextReq ← match forStagePlanOf suffixCtx b.pos tailKey restCl bd resultTy plan.outcome borrowNames plan.sourceSuspends with
              | .ok req => pure req
              | .error why => eerr b.pos s!"cannot type this waiting for's suffix: {why} (#417)"
            if !cA.types.loopRequests.any (·.key == nextReq.key) then
              modify fun st => { st with loopFirst := st.loopFirst ++
                [{ g := "", pos := b.pos, itemCode := .lit .void, argSet := none, lift := .ok nextReq }] }
              return (codeA, .prim .userErr [], if stagePlan.isSome then Ty.struct plan.base rootArgs else resultTy)
            let some nextPlan := nextReq.stagePlan | eerr b.pos "internal: missing suffix plan"
            let nextArgs := nextPlan.tparams.map fun tp =>
              (cA.types.tvars.lookup tp.name).getD (.param tp.name (tp.constraint == "comparable"))
            let nextCopies := nextPlan.copies.map (·.1)
            let nextBorrows := nextPlan.borrowed
            let suffix ← match forStagePrefixOf suffixCtx nextPlan nextArgs b.pos restCl bd (stageOverride.getD stageFlat) nextCopies nextBorrows with
              | .ok req => pure req
              | .error why => eerr b.pos s!"cannot share this waiting for's suffix: {why} (#335, #417)"
            if !cA.types.loopRequests.any (·.key == suffix.key) then
              modify fun st => { st with loopFirst := st.loopFirst ++
                [{ g := "", pos := b.pos, itemCode := .lit .void, argSet := none, lift := .ok suffix }] }
              return (codeA, .prim .userErr [], if stagePlan.isSome then Ty.struct plan.base rootArgs else resultTy)
            let stageTypes := rootArgs.map Ty.toSTy
            let consume (arm : SExpr) : SExpr :=
              let clauses := Choice.prepare [.decl b.pos b.name (some ty.toSTy) false arm]
                (choiceValues cA) (choiceField cA) (site := site) (fieldOrder := choiceOrder cA)
                (keepExcl := true) (keepBranches := choiceHasCast cA)
              let payload := site ++ "$suffix"
              let packet := payload ++ "$packet"
              let call := SExpr.app b.pos (.ident b.pos suffix.name) suffix.args true
              let get (j : Nat) := SExpr.app b.pos (.ident b.pos packet) [.int b.pos (j : Int)] false
              let tail : List SExpr := if nextCopies.isEmpty then [.decl b.pos payload none false call] else
                .decl b.pos packet none false call ::
                  (nextCopies.zipIdx.map fun (n, j) => .set b.pos (.ident b.pos n) none
                    (.app b.pos (.ident b.pos "$refineCopyOut") [get (j + 1)] false)) ++
                  [.decl b.pos payload none false (get 0)]
              let clauses := clauses ++ tail
              let body := forStageBodyAs bd (.app b.pos (.ident b.pos "$forResumeValues") [.ident b.pos payload, forStageCopyMetadata b.pos nextCopies, .block b.pos (nextBorrows.map (SExpr.ident b.pos ·))] false)
              if stagePlan.isSome then
                let stage := SExpr.app b.pos (.ident b.pos "$forStage")
                  [.str b.pos [.text plan.base], .decl b.pos "$stageView" (some (forStageView plan.base stageTypes)) false (.tuple b.pos []),
                    forStageCopyMetadata b.pos copyNames, .block b.pos (borrowNames.map (SExpr.ident b.pos ·)), .ident b.pos "false", .ident b.pos "true", .block b.pos clauses, body] false
                .optionLit b.pos (forClauseExitScope bd stage)
              else
              let prepare := SExpr.app b.pos (.ident b.pos "$forPrepare")
                [.str b.pos [.text plan.base], .decl b.pos "$stageView" (some (forStageView plan.base stageTypes)) false (.tuple b.pos []),
                  forStageCopyMetadata b.pos copyNames, .block b.pos (borrowNames.map (SExpr.ident b.pos ·)), .ident b.pos "true", .block b.pos clauses, body] false
              let code := if plan.copies.isEmpty then prepare else
                let packet := site ++ "$packet"
                let get (j : Nat) := SExpr.app b.pos (.ident b.pos packet) [.int b.pos (j : Int)] false
                SExpr.block b.pos (.decl b.pos packet none false prepare ::
                  (copyNames.zipIdx.map fun (n, j) => .set b.pos (.ident b.pos n) none
                    (.app b.pos (.ident b.pos "$refineCopyOut") [get (j + 1)] false)) ++ [get 0])
              .optionLit b.pos code
            let selected := Choice.consumeBranches i site consume
            let values ← elabE { cA with canFail := true, inTaking := true }
              (.query b.pos selected) none
            let slot ← fresh values.ty
            if stagePlan.isSome then
              let .arr value := values.ty | eerr b.pos "internal: prepared for environments"
              return (.seq codeA (.assign slot values.e), .local slot, value)
            let ready := site ++ "$ready"
            let c := { bodyCtx cA with
              canFail := sourceFail,
              locals := { name := ready, slot, ty := values.ty, mutable := false } :: cA.locals }
            let resumed ← elabE c (.app b.pos (.ident b.pos "$forResumeValues") [.ident b.pos ready, forStageCopyMetadata b.pos copyNames, .block b.pos (borrowNames.map (SExpr.ident b.pos ·))] false) none
            modify fun st => { st with forStageUses := st.forStageUses + 1 }
            let .arr value := resumed.ty | eerr b.pos "internal: staged for values"
            return (.seq codeA (.assign slot values.e), resumed.e, value)
          let cl := pruneMethodBinding cA (fs[j]?.getD (.tuple p []))
          let (f, a, t) ← exclIter cA (Choice.bifToExcl cl ++ after) more bd stageOverride
          return (.seq codeA f, a, t)
        let some (.decl gp x xty _ (.app _ _ alts _)) := fs[j]? | eerr p "internal: an exclusive choice"
        let altsS := alts.filter fun | .app _ (.ident _ "$joinOf") _ _ => false | _ => true
        -- (an `if`'s, #331, with no type written: its branches' join, as the
        -- `if`'s value has, found by elaborating it apart; that code is not kept)
        let xty ← match xty, alts.findSome? (fun | .app _ (.ident _ "$joinOf") (i :: l) false => some (i, l.head?) | _ => none) with
          | none, some (i, place) => do
            let st ← get
            -- (for `set L = if …`, at `L`'s type; a branch with a call to
            -- lift typed as `option{…}` takes it, #283)
            let (_, ty, _, _) ← elabBranchAlts { cA with canFail := true, inTaking := true, typeOnly := true } gp i none place
            restoreConstructProbe cA st
            pure (some ty.toSTy)
          | t, _ => pure t
        let alts : List (List SExpr × SExpr) := alts.filterMap fun
          | .app _ (.ident _ "$alt") [.block _ gs, r] false => some (gs, r)
          | _ => none
        -- (the selector: the first alternative whose guards hold)
        let selS : SExpr := alts.zipIdx.foldr (fun ((gs, _), i) acc =>
          .ite gp gs (.int gp (i : Int)) (some acc)) (.int gp (-1))
        let rsel ← elabE { cA with canFail := true, inTaking := true } selS (some .int)
        let sel ← fresh .int
        -- (a path's clauses: its guards, then its value bound to the choice's name)
        let liftP (gs : List SExpr) (r : SExpr) (i : Nat) : List SExpr :=
          let rcl : List SExpr := match r with
            | .block rp ss => match ss.getLast? with
              | some (.decl q y t v e) => ss.dropLast ++ [.decl q y t v e, .decl rp x xty false (.ident rp y)]
              | some l => ss.dropLast ++ [.decl rp x xty false l]
              | none => [.decl rp x xty false (.tuple rp [])]
            | e => [.decl e.pos x xty false e]
          normGens (Choice.prepare (gs ++ rcl) (choiceValues cA) (choiceField cA)
            (site := s!"$x{x}a{i}") (fieldOrder := choiceOrder cA) (keepExcl := true)
            (keepBranches := choiceHasCast cA))
        -- (a path: its clauses up to its first generator into this filter, its
        -- generators into the body, with `pb` as the body; `flat`: `pb` is an
        -- array of the values, a continuation's, to flatten)
        let runPath (cl : List SExpr) (pb : SExpr) (flat : Bool) : EM (Expr × Expr × Ty) := do
          let transfer := if stagePlan.isSome && flat then some true else stageOverride
          let (f, a, t) ← exclIter cA (cl.takeWhile (!isGen ·)) (groups (cl.dropWhile (!isGen ·))) pb transfer
          if !flat || stagePlan.isSome then return (f, a, t)
          match t with
          | .arr t' => return (f, .prim .flatten [a], t')
          | _ => eerr gp "internal: a continuation's values"
        -- (#335, phase 2b: another such choice, or an exclusive one, in the
        -- clauses after it, and a body that may run in a failure context:
        -- those clauses and the body a function of their own, #342's, which
        -- each path calls, instead of a copy in each)
        let restCl := after ++ moreCl
        let staged ← if restCl.any isCF then
            match xty with
            | some ty => do
              let bty ← resolveTy cA.types gp ty
              stagedSuffix cA gp x bty altsS restCl bd stageOverride
            | none => pure none
          else pure none
        if let some (_, _, value, false) := staged then
          let value := (stagePlan.map fun plan => Ty.struct plan.base stageArgs).getD value
          return (codeA, .prim .userErr [], value)
        let contOK := stagePlan.isNone && restCl.any isCF && forBodySafe cA bd && xty.isSome
        let req := if !contOK || cA.typeOnly then none else
          cA.types.loopRequests.find? (·.key == (if bodyFail then "fo" else "f") ++ contKey cA gp x (altsS ++ restCl ++ [bd]))
        let fits (l : Choice.FirstLift) : Bool :=
          cA.acceptsHelper l
        let kv := s!"$xk{gp.line}_{gp.col}{x}v"
        let plan : List (List SExpr × SExpr × Bool) ← if let some (prepare, plan, _, true) := staged then
            let (callCl, resumed) := forStageInvoke gp prepare plan.borrowed bd
            pure (alts.zipIdx.map fun ((gs, r), i) => (liftP gs r i ++ callCl, resumed, true))
          else match req with
          | some l =>
            if fits l then
              let call : SExpr := .app gp (.ident gp l.name) l.args true
              let callCl : List SExpr := if l.sets.isEmpty then [.decl gp kv none false call] else
                let kt := s!"$xk{gp.line}_{gp.col}{x}t"
                [.decl gp kt none false call] ++
                  l.sets.zipIdx.map (fun (m, j) => SExpr.set gp (.ident gp m) none (.app gp (.ident gp kt) [.int gp ((j + 1 : Nat) : Int)] false)) ++
                  [.decl gp kv none false (.app gp (.ident gp kt) [.int gp 0] false)]
              let vals : SExpr := if bodyFail then .app gp (.ident gp "$forOutcomeValues") [.ident gp kv] false else .ident gp kv
              pure (alts.zipIdx.map fun ((gs, r), i) => (liftP gs r i ++ callCl, vals, true))
            else pure (alts.zipIdx.map fun ((gs, r), i) => (liftP gs r i ++ restCl, bd, false))
          | none =>
            -- (the first elaboration: the first path with the clauses after
            -- it and the body, for the values' type, which asks for the
            -- function; its code is not kept, as the next round compiles all)
            if let (true, some ((gs0, r0), some sty)) := (contOK && !cA.typeOnly, alts.head?.map (·, xty)) then
              let bty ← resolveTy cA.types gp sty
              -- (what refuses it known before the trial, which then costs
              -- nothing: all but the values' type, #364's review)
              if (contForLiftOf cA gp x bty .void altsS restCl bd bodyFail).toOption.isSome then
                let st0 ← get
                let (f0, a0, t0) ← runPath (liftP gs0 r0 0 ++ restCl) bd false
                if forContWaits cA st0 (← get) [f0, a0] then set st0 else
                  match contForLiftOf cA gp x bty t0 altsS restCl bd bodyFail with
                  | .ok lift =>
                    if cA.suspends then restoreForContTrial st0
                    let use : LoopUse := { g := "", pos := gp, itemCode := .lit .void, argSet := none, lift := .ok lift }
                    modify fun st => { st with loopFirst := st.loopFirst ++ [use] }
                    if cA.suspends then return (codeA, .prim .userErr [], t0)
                    return (Expr.seq codeA f0, a0, t0)
                  | .error _ => set st0
            pure (alts.zipIdx.map fun ((gs, r), i) => (liftP gs r i ++ restCl, bd, false))
        let mut filts : Array Expr := #[]
        let mut arrs : Array Expr := #[]
        let mut ety : Option Ty := none
        for (cl, pb, flat) in plan do
          let (f, a, t) ← runPath cl pb flat
          if let some t0 := ety then
            if t0 != t then eerr gp s!"the for's values have the type {t0.show} on one path of this if and {t.show} on another"
          ety := some t
          filts := filts.push f
          arrs := arrs.push a
        let some t := ety | eerr gp "internal: an exclusive choice without alternatives"
        let pick (es : Array Expr) (last : Expr) : Expr :=
          (es.toList.zipIdx.foldr (fun (e, i) acc => .ite (p2 .eq (.local sel) (.lit (.int (i : Int)))) e acc) last)
        -- (each path's filter as `void`, as `failV` is, for the if-chain)
        let filt := Expr.seq codeA (.seq (.assign sel rsel.e)
          (pick (filts.map fun f => Expr.seq f (.lit .void)) Expr.failV))
        return (filt, pick arrs (.lit Value.emptyArray), t)
    match gs with
    | [] =>
      let r ← elabE (bodyCtx c) bd none
      -- The generated arrays must infer their element type during
      -- suspension lowering. As for array/tuple literals, a body that
      -- never completes has Core's void type without changing its exit.
      let r := if r.ty == .never then { r with e := .seq r.e (.lit .void) } else r
      if let some failed := failure then
        -- Waiting source bodies cannot fail. Their explicit source exits
        -- already return packets, so no failure-capture rewrite is needed.
        if c.suspends && !r.e.mayFail ctx.sigProg then return r
        let packet ← elabE { c with canFail := false } failed (some c.retTy)
        let hint ← fresh (.opt r.ty)
        return ⟨FailCapture.marked hint r.e (.ret packet.e), r.ty⟩
      return r
    | (g, fs) :: more =>
      let declare (c : Ctx) (n : String) (ty : Ty) : EM (Nat × Ctx) := do
        if c.lookup n |>.isSome then eerr g.pos s!"'{n}' is already defined"
        let slot ← fresh ty
        return (slot, { c with locals := { name := n, slot, ty, mutable := false } :: c.locals })
      -- (a choice whose alternatives have several values themselves, or
      -- clauses to lift, #283: a for of its own for each alternative, with
      -- the clauses after it and the body, their values concatenated, so
      -- that each alternative's values come in order, with the body between)
      if let some b@{ pos := gp, place := none, branchy := none, each := none, .. } := Choice.binding? g then
        if b.alts.any Choice.hasLiftable then
          -- (with the binding's name: an inlined body's position is every
          -- site's, #314)
          let site := s!"$cf{gp.line}_{gp.col}{b.name}"
          let moreClauses := more.flatMap fun (g', fs') => g' :: fs'
          let bctx : Ctx := { c with canFail := ctx.canFail, inTaking := ctx.inTaking, inLoop := ctx.inLoop,
                                     inRepeat := ctx.inRepeat }
          let liftA (a : SExpr) (i : Nat) : List SExpr :=
            -- (its exclusive choices kept: this for compiles them, #314)
            Choice.prepare [.decl gp b.name b.ty false a] (choiceValues c) (choiceField c)
              (fieldOrder := choiceOrder c)
              (site := s!"{site}a{i}") (keepExcl := true) (keepBranches := choiceHasCast c)
          let forW (cl : List SExpr) (bd : SExpr) : EM R :=
            elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq bctx p cl bd
              (prepared := true) (failure := failure)
          -- (#335, phase 2: another such choice, or an exclusive one, in the
          -- clauses after it, and a body that may run in a failure context:
          -- those clauses and the body a function of their own, which each
          -- alternative's for calls, instead of a copy in each)
          let restCl := fs ++ moreClauses
          if restCl.any isCF && c.suspends then
            let saved ← get
            let mut types : List Ty := []
            for (a, i) in b.alts.zipIdx do
              let r ← elabForWith elabAlts elabBranchAlts elabE elabInts elabLoopGen elabSeq
                { bctx with typeOnly := true } p (liftA a i) (.ident gp b.name) (prepared := true)
              if let .arr t := r.ty then types := types ++ [t]
            set saved
            if let some bty := types.head? then
              if types.length == b.alts.length && types.all (· == bty) then
                if let some (prepare, plan, value, ready) ← stagedSuffix c gp b.name bty b.alts restCl bd then
                  if !ready then return ⟨.prim .userErr [], .arr value⟩
                  let (callCl, resumed) := forStageInvoke gp prepare plan.borrowed bd
                  let mut parts : List R := []
                  for (a, i) in b.alts.zipIdx do
                    let r ← forW (liftA a i ++ callCl) resumed
                    let .arr (.arr t) := r.ty | eerr gp "internal: a staged continuation's values"
                    parts := parts ++ [⟨.prim .flatten [r.e], .arr t⟩]
                  let some first := parts.head? | eerr gp "internal: a choice without alternatives"
                  return ⟨parts.tail.foldl (fun acc r => p2 .concat acc r.e) first.e, first.ty⟩
          -- Failable bodies return outcomes so failure stops the entire
          -- for, rather than merely rejecting one continuation call.
          if restCl.any isCF && forBodySafe c bd then
            let req := if c.typeOnly then none else
              c.types.loopRequests.find? (·.key == (if bodyFail then "fo" else "f") ++ contKey c gp b.name (b.alts ++ restCl ++ [bd]))
            let fits (l : Choice.FirstLift) : Bool :=
              c.acceptsHelper l
            if let some l := req then
              if fits l then
                let kv := s!"{site}v"
                let mut parts : List R := []
                for (a, i) in b.alts.zipIdx do
                  let call : SExpr := .app gp (.ident gp l.name) l.args true
                  let callCl : List SExpr := if l.sets.isEmpty then [.decl gp kv none false call] else
                    let kt := s!"{site}t"
                    [.decl gp kt none false call] ++
                      l.sets.zipIdx.map (fun (m, j) => SExpr.set gp (.ident gp m) none (.app gp (.ident gp kt) [.int gp ((j + 1 : Nat) : Int)] false)) ++
                      [.decl gp kv none false (.app gp (.ident gp kt) [.int gp 0] false)]
                  let vals : SExpr := if bodyFail then .app gp (.ident gp "$forOutcomeValues") [.ident gp kv] false else .ident gp kv
                  let r ← forW (liftA a i ++ callCl) vals
                  match r.ty with
                  | .arr (.arr t) => parts := parts ++ [⟨.prim .flatten [r.e], .arr t⟩]
                  | _ => eerr gp "internal: a continuation's values"
                let some r0 := parts.head? | eerr gp "internal: a choice without alternatives"
                return ⟨parts.tail.foldl (fun acc r => p2 .concat acc r.e) r0.e, r0.ty⟩
            else if let some a0 := b.alts.head? then
              -- (the first elaboration: each alternative alone, for its
              -- binding's type, and the first with the clauses after it and
              -- the body, for the values' type; its code is not kept)
              let st0 ← get
              let mut tys : List Ty := []
              for (a, i) in b.alts.zipIdx do
                let r ← forW (liftA a i) (.ident gp b.name)
                if let .arr t := r.ty then tys := tys ++ [t]
              let same := tys.length == b.alts.length && tys.all (some · == tys.head?)
              -- (what refuses it known before the trial, which then costs nothing)
              -- (all its refusals but the values' type, #364's review)
              let known : Bool := match tys.head? with
                | some bty => (contForLiftOf c gp b.name bty .void b.alts restCl bd bodyFail).toOption.isSome
                | none => false
              if same && known then
                let r0 ← forW (liftA a0 0 ++ restCl) bd
                if forContWaits c st0 (← get) [r0.e] then set st0 else
                  match (do
                      let some bty := tys.head? | throw "no type"
                      let .arr vty := r0.ty | throw "no values"
                      contForLiftOf c gp b.name bty vty b.alts restCl bd bodyFail) with
                  | .ok lift =>
                    if c.suspends then restoreForContTrial st0
                    let use : LoopUse := { g := "", pos := gp, itemCode := .lit .void, argSet := none, lift := .ok lift }
                    modify fun st => { st with loopFirst := st.loopFirst ++ [use] }
                    if c.suspends then return ⟨.prim .userErr [], r0.ty⟩
                    return r0
                  | .error _ => set st0
              else set st0
          let mut parts : List R := []
          for (a, i) in b.alts.zipIdx do
            parts := parts ++ [← forW (liftA a i ++ fs ++ moreClauses) bd]
          let some r0 := parts.head? | eerr gp "internal: a choice without alternatives"
          if let some r := parts.find? (·.ty != r0.ty) then
            eerr gp s!"the for's values have the type {r0.ty.show} for one alternative of this choice and {r.ty.show} for another"
          return ⟨parts.tail.foldl (fun acc r => p2 .concat acc r.e) r0.e, r0.ty⟩
      -- (a call of a recursive function with several values taken lazily,
      -- #246: a loop over its values, each one iteration, over a one-element
      -- array, whose filter binds it and runs the generator's filters, and
      -- whose values are collected)
      if let some { pos := gp, name := n, ty := sty, each := some (.app _ (.ident _ "$loop") lp false), .. } :=
          Choice.binding? g then
        let lg ← elabLoopGen { c with canFail := true, inTaking := true } gp lp
        let ty ← match ← sty.mapM (resolveTy c.types gp) with
          | some t => pure t
          | none => pure lg.vty
        let (xs, c1) ← declare c n ty
        -- (the iteration's values, their type, and whether they are flat
        -- already: with an exclusive choice among the filters, #314, its
        -- paths in this filter and their values, flattened)
        let (iter, ity, flat) ← if fs.any isExcl then do
            let (filtE, arr, ety) ← exclIter c1 fs more bd flatOverride
            let bindX ← coerce gp ⟨lg.value, lg.vty⟩ ty
            let one ← fresh .void
            pure (Expr.prim .flatten [.forE one (.lit (.arr #[.tup []])) (.seq (.assign xs bindX) filtE) arr],
              ety, true)
          else do
            let (filt, c2) ← elabFilters c1 fs
            let bindX ← coerce gp ⟨lg.value, lg.vty⟩ ty
            let inner ← build c2 more bd (flatOverride := flatOverride)
            let one ← fresh .void
            pure (Expr.forE one (.lit (.arr #[.tup []])) (.seq (.assign xs bindX) filt) inner.e,
              inner.ty, more.isEmpty)
        -- (the steps in rounds, each a `forE` over a range twice as long as
        -- the last one's, whose body runs a step and gives the values of
        -- its iteration, if it came to a value: so the values are collected
        -- in linear time and space, where adding each to an array would copy
        -- it each time)
        let acc ← fresh (.arr ity)
        let size ← fresh .int
        let done ← fresh .logic
        let d ← fresh .int
        let vd : Expr := .lit .void
        let none : Expr := .lit Value.emptyArray
        let r ← fresh (.arr ity)
        let stepBody : Expr := .ite (p2 .eq (.local lg.sp) (.lit (.int 0)))
          (.seq (.assign done (.lit (.logic true))) none)
          (.seq lg.step (.ite (.prim .query [.local lg.has])
            (.seq (.assign r iter) (.seq lg.after (.local r))) none))
        let round : Expr := .forE d (p2 .range (.lit (.int 1)) (.local size))
          (p2 .eq (.local done) (.lit (.logic false))) stepBody
        let body : Expr := .seq (.assign acc (p2 .concat (.local acc) (.prim .flatten [round])))
          (.ite (p2 .eq (.local done) (.lit (.logic true))) Expr.brkV
            (.seq (.assign size (p2 .mul (.local size) (.lit (.int 2)))) vd))
        -- A nested continuation's failed outcome breaks the nearest loop.
        -- This producer catches that break before the private outcome loop,
        -- so forward it before any enclosing generator can run another item.
        let values := match c.forOutcomeSlot with
          | some flag => Expr.ite (.prim .query [.local flag]) (.local acc)
              (.seq .brk (.prim .userErr []))
          | none => Expr.local acc
        -- A source break has already run its lexical cleanup. Every lazy
        -- loop crossed must forward it without exposing accumulated values.
        let values := match c.forBreakSlot with
          | some flag => Expr.ite (.prim .query [.local flag])
              (.seq .brk (.prim .userErr [])) values
          | none => values
        let code : Expr := .seq lg.init (.seq (.assign acc none) (.seq (.assign size (.lit (.int 16)))
          (.seq (.assign done (.lit (.logic false))) (.seq (.loop body) values))))
        if flat then return ⟨code, .arr ity⟩
        match ity with
        | .arr t => return ⟨.prim .flatten [code], .arr t⟩
        | _ => eerr gp "internal: nested for"
      -- the source: evaluated before the iterations; a failing source gives no iterations
      let (slot, src, c1, pre) ← match g with
        | .decl gp n none false (.range _ lo hi) => do
          let es ← elabInts { c with canFail := true, inTaking := true } gp [lo, hi]
          let (slot, c1) ← declare c n .int
          pure (slot, Expr.prim .range es, c1, Expr.lit (.logic true))
        | .gen gp x idx srcE => do
          let rs ← elabE { c with canFail := true, inTaking := true } srcE none
          match rs.ty with
          | .map kt vt =>
            -- `for (V : M)` and `for (K -> V : M)`: over the (key, value) pairs
            let tmp ← fresh rs.ty
            let src := if (rs.e.mayFail ctx.sigProg) then
                Expr.orE tmp rs.e (.lit Value.emptyArray) else rs.e
            let tp ← fresh (.tup [kt, vt])
            let (pre, c1) ← match idx with
              | none => do
                let (xs, c1) ← declare c x vt
                pure (Expr.assign xs (.prim (.tupGet 1) [.local tp]), c1)
              | some i => do
                let (is, c1) ← declare c i kt
                let (xs, c2) ← declare c1 x vt
                pure (Expr.seq (.assign is (.prim (.tupGet 0) [.local tp]))
                  (.assign xs (.prim (.tupGet 1) [.local tp])), c2)
            pure (tp, src, c1, pre)
          | _ =>
          match idx with
          | some i => do
            -- `I -> X : A`: iterate over the indices of A
            let ty ← match rs.ty with
              | .arr t => pure t
              | t => eerr gp s!"a for generator needs an array, string or map, found {t.show}"
            let tmp ← fresh rs.ty
            let src0 := if (rs.e.mayFail ctx.sigProg) then
                Expr.orE tmp rs.e (.lit Value.emptyArray) else rs.e
            let ta ← fresh rs.ty
            let (islot, c1) ← declare c i .int
            let (xslot, c2) ← declare c1 x ty
            let src := Expr.seq (.assign ta src0)
              (.prim .range [.lit (.int 0), p2 .sub (.prim .len [.local ta]) (.lit (.int 1))])
            pure (islot, src, c2, Expr.assign xslot (p2 .index (.local ta) (.local islot)))
          | none => do
          let ty ← match rs.ty with
            | .arr t => pure t
            | t => eerr gp s!"a for generator needs an array, string or map, found {t.show}"
          let tmp ← fresh rs.ty
          let src := if (rs.e.mayFail ctx.sigProg) then
              Expr.orE tmp rs.e (.lit Value.emptyArray) else rs.e
          let (slot, c1) ← declare c x ty
          pure (slot, src, c1, Expr.lit (.logic true))
        | .decl gp n _ false _ => do
          -- `X := a₁ | … | aₙ` (#208): over the alternatives' indices, each
          -- alternative bound in the filter (so a failing one is skipped)
          let some b := Choice.binding? g | eerr g.pos "bad for clause"
          -- (an `if` with choices in its branches picks its branch first, once, #235)
          let (pre, ty, es, _) ← match b.branchy with
            | some i => elabBranchAlts { c with canFail := true, inTaking := true } gp i b.ty b.place
            | none => do let (ty, es) ← elabAlts { c with canFail := true } gp b; pure (none, ty, es, false)
          checkNewLocal c gp n
          let k ← fresh .int
          let (xs, c1) ← declare c n ty
          let idx := Expr.lit (.arr (choiceIdx es.length))
          pure (k, (pre.map (Expr.seq · idx)).getD idx, c1, Expr.assign xs (Expr.altE k es))
        | _ => eerr g.pos "bad for clause"
      -- (an exclusive choice among the filters, #314: its paths in this
      -- iteration's filter, so that a failure in one rolls back to this
      -- generator, as the `if` it stands for would)
      if fs.any isExcl then
        let (filtE, arr, ety) ← exclIter c1 fs more bd flatOverride
        let filt := match pre with
          | .lit _ => filtE
          | e => .seq e filtE
        return ⟨.prim .flatten [Expr.forE slot src filt arr], .arr ety⟩
      let (filt, c2) ← elabFilters c1 fs
      let filt := if fs.isEmpty then pre else
        match pre with
        | .lit _ => filt
        | e => .seq e filt
      let inner ← build c2 more bd (flatOverride := flatOverride)
      let loopE := Expr.forE slot src filt inner.e
      match more with
      | [] => return ⟨loopE, .arr inner.ty⟩
      | _ =>
        match inner.ty with
        | .arr t => return ⟨.prim .flatten [loopE], .arr t⟩
        | _ => eerr p "internal: nested for"
  match pre with
  | [] =>
    let r ← build ctx gs body
    if firstDecides && gs.isEmpty then return ⟨.prim .mkArr [r.e], .arr r.ty⟩
    return r
  | _ =>
    -- (an exclusive choice among them, #314: its paths in this filter)
    -- (through a generator over one element, whose filters they are)
    if pre.any isExcl then
      -- (named for the depth too: a for of an alternative's, inside this
      -- one's clauses, has the same position)
      let r ← build ctx ((.gen p s!"$u{p.line}_{p.col}_{ctx.locals.length}" none (.arrayLit p [.tuple p []]), pre) :: gs) body false
      -- (a continuation's, #335: its filter, then its values, failing where
      -- the filter fails, as the caller's filter would with it copied in)
      if firstDecides then
        match r.e with
        | .prim .flatten [.forE _ _ filt arr] => return ⟨.seq filt arr, r.ty⟩
        | _ => eerr p "internal: a continuation's clauses"
      return r
    -- filters before any generator: iterate once over a one-element array
    let (filt, c1) ← elabFilters ctx pre
    let slot ← fresh .void
    let inner ← build c1 gs body
    match gs with
    | [] =>
      if firstDecides then return ⟨.seq filt (.prim .mkArr [inner.e]), .arr inner.ty⟩
      return ⟨.forE slot (.lit (.arr #[.tup []])) filt inner.e, .arr inner.ty⟩
    | _ =>
      match inner.ty with
      | .arr t =>
        if firstDecides then return ⟨.seq filt inner.e, .arr t⟩
        return ⟨.prim .flatten [.forE slot (.lit (.arr #[.tup []])) filt inner.e], .arr t⟩
      | _ => eerr p "internal: nested for"

/-- Bare type names written in a default, excluding names bound by a local
    generic struct. Parametric type heads name declarations, not aliases. -/
partial def defaultTypeNames (bound : List String) (e : SExpr) : List String :=
  let bare := fun (t : STy) => (t.bareNames.filter (!bound.contains ·))
  match e with
  | .structDef _ tps fs =>
    let own := bound ++ tps.map (·.name)
    fs.flatMap fun (_, t, d, _) => t.bareNames.filter (!own.contains ·) ++
      (d.toList.flatMap (defaultTypeNames own))
  | _ =>
    let own := match e with
      | .decl _ _ (some t) _ _ | .refineDef _ _ t _ => bare t
      | .construct _ _ ts _ => ts.flatMap bare
      | _ => []
    own ++ e.children.flatMap (defaultTypeNames bound)

/-- Rename a default's type aliases without capturing a local struct's
    parameters. Its nested consumers retain their own type binders. -/
partial def substDefaultTypes (σ : List (String × STy)) (e : SExpr) : SExpr :=
  Choice.mapE (fun
    | .decl p n t v x => some (.decl p n (t.map (·.substNames σ)) v (substDefaultTypes σ x))
    | .construct p n ts fs => some (.construct p n (ts.map (·.substNames σ)) (fs.map (substDefaultTypes σ)))
    | .refineDef p n t cs => some (.refineDef p n (t.substNames σ) (cs.map (substDefaultTypes σ)))
    | .structDef p tps fs =>
      let σ' := σ.filter fun (n, _) => !tps.any (·.name == n)
      some (.structDef p tps (fs.map fun (n, t, d, v) =>
        (n, t.substNames σ', d.map (substDefaultTypes σ'), v)))
    | .app p (.ident q "$witness") [.ident r n] false =>
      match σ.lookup n with
      | some (.name v) => some (.app p (.ident q "$witness") [.ident r v] false)
      | _ => none
    | _ => none) e

/-- Default source annotations use private aliases for the callee's
    instantiations. Generated annotations keep the actual Core names, even
    when the caller and callee use the same names in a different order. -/
def defaultTypes (ctx : Ctx) (p : Pos) (s : Sig) (σ : List (String × Ty)) (d : SExpr) : EM (TyEnv × SExpr) := do
  let core := Ty.mergeParamBounds (σ.flatMap fun (_, t) => t.paramsC)
  let foreign := core.filter fun (n, _) => !s.tparams.any (·.1 == n)
  let names := defaultTypeNames [] d
  let home := { ctx.types with tvars := σ }
  for (n, _) in foreign do
    if names.contains n then
      discard <| resolveTy home p (.name n)
  let alias (n : String) := s!"$defaultType_{s.name}_{n}"
  let rename := s.tparams.map fun (n, _) => (n, STy.name (alias n))
  for (n, _) in s.tparams do
    if names.contains n && (σ.lookup n).isNone then
      eerr p s!"cannot infer type parameter {n} of {s.name} from the arguments of this call"
  let aliases := σ.map fun (n, t) => (alias n, t)
  return ({ ctx.types with tvars := aliases ++ core.map (fun (n, cmp) => (n, Ty.param n cmp)) },
    substDefaultTypes rename d)

/-- A call of a generic function. Its type arguments are inferred by matching
    its signature: the result type against the expected type (unless that is
    `void`, which accepts anything), then each parameter type against its
    argument's, left to right. An argument whose parameter type is already
    determined is elaborated against it, so `array{}` and `false` work. -/
partial def elabGenericCallWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (p : Pos) (s : Sig) (args : List SExpr) (exp : Option Ty)
    (packArgs : Bool := false) (inst : List (String × Ty) := []) :
    EM R := do
  let s := if packArgs then { s with ret := .tup s.params } else s
  -- named arguments (#119): positional ones, then named ones as written,
  -- then the defaults of those omitted, as for other functions
  let isNamed : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
  let npos := s.params.length - s.named.length
  let pos := args.filter (!isNamed ·)
  let named : List (Pos × String × SExpr) := args.filterMap fun
    | .decl ap n _ _ rhs => if n.startsWith "?" then some (ap, (n.drop 1).toString, rhs) else none
    | _ => none
  let plain := s.named.isEmpty && named.isEmpty
  if plain then
    if args.length != s.params.length then
      eerr p s!"{s.name} takes {s.params.length} argument(s), found {args.length}"
  else
    if pos.length != npos then
      -- (a method's receiver is its first positional argument)
      let (shown, off) := match s.name.splitOn "." with
        | [_, m] => if s.pnames.head? == some "Self" then (m, 1) else (s.name, 0)
        | _ => (s.name, 0)
      eerr p s!"{shown} takes {npos - off} positional argument(s), found {pos.length - off}"
    for ((ap, n, _), i) in named.zip (List.range named.length) do
      if (s.named.find? (·.1 == n)).isNone then eerr ap s!"{s.name} has no parameter ?{n}"
      if (named.take i).any (·.2.1 == n) then eerr ap s!"?{n} is given twice"
  -- the arguments given, in the order they are evaluated, each with the
  -- index of its parameter
  let given : List (SExpr × Nat) := (pos.zip (List.range npos)) ++ named.map fun (_, n, rhs) =>
    (rhs, npos + (s.named.findIdx? (·.1 == n)).getD 0)
  let ptys := s.params.toArray
  let mut σ : List (String × Ty) := inst
  -- Member dispatch has already saved the receiver in a typed local. Its
  -- class arguments are fixed even when the expected result could infer a
  -- wider type (or an argument is `false`); only method-local parameters
  -- remain available for result-directed inference.
  if s.pnames.head? == some "Self" || s.pnames.head? == some "$Self" then
    if let (some (.struct owner patterns), some (.ident _ recv, _)) := (s.params.head?, given.head?) then
      if let some binding := ctx.lookup recv then
        if let .struct cls ts := binding.ty then
          if ctx.types.isSub cls owner then
            let fixed := (patterns.zip (ctx.types.upArgs cls ts owner)).filterMap fun
              | (.param n _, t) => some (n, t)
              | _ => none
            σ := σ ++ fixed.filter (fun (n, _) => (σ.lookup n).isNone)
  if let some et := exp then
    if !(et == .void) then
      if let some σ' := s.ret.matchArg ctx.types σ et then σ := σ'
  let bound (σ : List (String × Ty)) (t : Ty) := t.params.all fun v => (σ.lookup v).isSome
  -- Empty values and generic function identifiers need an expected type,
  -- so elaborate them after other arguments, while still evaluating in order.
  let contextual := (← given.mapM (fun (a, _) => argNeedsTypeWith elabE ctx a)).toArray
  let mut es : Array Expr := Array.replicate given.length (.lit .void)
  -- arguments left for the second pass; an argument whose type contains
  -- `false` (like `array{Err()}`) binds nothing, so it joins them
  let mut deferred : Array Bool := contextual
  for pass in [0, 1] do
    for ((a, k), i) in given.zip (List.range given.length) do
      let pt := ptys[k]!
      if (pass == 0) == deferred[i]! then continue
      if bound σ pt then
        let t := pt.subst σ
        let r ← elabE ctx a (some t)
        let e ← tryCatch (coerce a.pos r t) fun msg => throw s!"{msg} (in a call of {s.name})"
        es := es.set! i e
      else
        if contextual[i]! then
          let v := (pt.params.filter fun v => (σ.lookup v).isNone).headD "t"
          eerr a.pos s!"cannot infer type parameter {v} of {s.name} from the arguments of this call"
        let r ← elabE ctx a none
        match pt.matchArg ctx.types σ r.ty with
        | some σ' =>
          σ := σ'
          if pass == 0 && !bound σ pt then
            deferred := deferred.set! i true
          else
            es := es.set! i (← coerce a.pos r (pt.subst σ))
        | none => eerr a.pos s!"expected {(pt.subst σ).show}, found {r.ty.show} (in a call of {s.name})"
  -- the arguments, in their temporaries, then the defaults
  let mut steps : Array Expr := #[]
  let mut slots : Array (Option Nat) := Array.replicate s.params.length none
  if !plain then
    for ((_, k), i) in given.zip (List.range given.length) do
      let ta ← fresh (ptys[k]!.subst σ)
      steps := steps.push (.assign ta es[i]!)
      slots := slots.set! k (some ta)
    for ((n, dflt), j) in s.named.zip (List.range s.named.length) do
      let k := npos + j
      if slots[k]!.isNone then
        let some d := dflt | eerr p s!"{s.name} needs the argument ?{n}, which has no default"
        let pt := ptys[k]!
        -- (the default sees the parameters before it, in their temporaries)
        let earlier : List Local := ((s.pnames.zip (List.range k)).filterMap fun (pn, j) =>
          (slots[j]!).map fun sl => ({ name := pn, slot := sl, ty := ptys[j]!.subst σ, mutable := false } : Local)).reverse
        let key := (s.name, s!"?{n}")
        if ctx.defaults.contains key then
          eerr p s!"the default of ?{n} of {s.name} uses itself (a call of {s.name} that omits ?{n})"
        -- (a method's: its receiver's fields too, through `Self`; a copy's
        -- in its interface's scope, as its body, #53)
        let selfC : Option String :=
          if s.pnames.head? == some "Self" then s.scope.orElse fun _ => (s.name.splitOn ".").head? else none
        -- Written types belong to the callee, with the arguments inferred
        -- so far. A caller's type aliases are outside this default's scope.
        let (types, d) ← defaultTypes ctx p s σ d
        let dctx := { ctx with locals := earlier, selfClass := selfC,
                               selfMethod := if selfC.isSome then (s.name.splitOn ".").getLast? else none,
                               inParamDefault := true,
                               types,
                               inLoop := false, canFail := ctx.canFail && s.decides,
                               suspends := ctx.suspends && s.suspends,
                               defaults := key :: ctx.defaults }
        -- (its type: the parameter's, or what the default gives a type
        -- parameter nothing else determined)
        let σ0 := σ
        if !bound σ0 pt && (← argNeedsTypeWith elabE dctx d) then
          let v := (pt.params.filter fun v => (σ0.lookup v).isNone).headD "t"
          eerr p s!"cannot infer type parameter {v} of {s.name} from the arguments of this call"
        let (rd, σ1) ← fxAt p (do
          let r ← elabE dctx d (if bound σ0 pt then some (pt.subst σ0) else none)
          let σ1 ← if bound σ0 pt then pure σ0 else
            match pt.matchArg ctx.types σ0 r.ty with
            | some σ' => pure σ'
            | none => eerr p s!"the default of ?{n} of {s.name} is a {r.ty.show}, not a {(pt.subst σ0).show}"
          return (← coerce p r (pt.subst σ1), σ1))
        σ := σ1
        if !s.decides && rd.mayFail ctx.sigProg then
          eerr p s!"the default of ?{n} of {s.name} can fail, but {s.name} is not <decides>"
        let ta ← fresh (pt.subst σ)
        steps := steps.push (.assign ta rd)
        slots := slots.set! k (some ta)
  let mut targs : Array Ty := #[]
  for (v, cmp) in s.tparams do
    let some t := σ.lookup v
      | eerr p s!"cannot infer type parameter {v} of {s.name} from the arguments of this call"
    -- (not of a value class's `$call…`, #218: the class's type arguments
    -- are its receiver's, fixed, and checked, when the value was made; a
    -- call through a function type only dispatches to it)
    let valueCall := !(s.name.splitOn ".$call").tail.isEmpty
    if cmp && !valueCall && !t.comparable ctx.types then
      eerr p (notComparable ctx.types t s!"type parameter {v} of {s.name}")
    targs := targs.push t
  -- A lazy recursive edge needs the ordinary call's arguments/defaults,
  -- evaluated once in order, before pushing its next producer item.
  if ctx.typeOnly && ctx.callInstanceProbe == some s.name then
    return ⟨.lit .void, .tup targs.toList⟩
  if packArgs then
    let values := if plain then es.toList else slots.toList.map (fun o => Expr.local o.get!)
    return ⟨steps.toList.foldr Expr.seq (.prim .mkTup values), s.ret.subst σ⟩
  -- the hidden arguments: a value of each type argument (but those a
  -- method reads from its receiver, #209)
  -- (in a dispatch's branch that opens type arguments, #209, a type
  -- argument in terms of the caller's own type parameters, whose values the
  -- dispatch types under its refinement; one that still mentions the opened
  -- ones has no value to pass)
  let dicts ← ((targs.toList.zip s.tparams).filter fun (_, (v, _)) => !s.selfTps.contains v).mapM
    fun (t, (v, _)) => do
      let t := t.unrefine ctx.unrefine
      if t.params.any (·.startsWith "$ext") then
        eerr p s!"cannot call {s.name} here yet: its type parameter {v} would mention type arguments that the dispatch opens, apart from the caller's, and no value of those can be passed (#209)"
      witness ctx.types ctx.dictBase ctx.dictVars t
  if plain then return ⟨.call s.idx (es.toList ++ dicts), s.ret.subst σ⟩
  let call := Expr.call s.idx (slots.toList.map (fun o => Expr.local o.get!) ++ dicts)
  return ⟨steps.toList.foldr Expr.seq call, s.ret.subst σ⟩

/-- Bind a recursive edge at the producer's current parameter instance.
    Expand a tuple before appending a first-success helper's captures, with
    a method's receiver evaluated before its tuple. Normal call binding
    still checks the projections and evaluates named arguments and defaults. -/
def elabRecursiveArgsWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (p : Pos)
    (sig : Sig) (args : List SExpr) (types : List Ty) (inst : List (String × Ty) := []) : EM R := do
  let ty := Ty.tup types
  let isNamed : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
  let pos := args.filter (!isNamed ·)
  let off := if sig.pnames.head? == some "$Self" then 1 else 0
  let npos := sig.params.length - sig.named.length
  if pos.length != off + 1 || npos < off + 2 then
    return ← elabGenericCallWith elabE ctx p sig args (some ty) (packArgs := true) (inst := inst)
  let mut ctx' := ctx
  let mut pre : List Expr := []
  let mut receiverArgs : List SExpr := []
  if off == 1 then
    let receiver := pos[0]!
    let rt := types[0]!
    let r ← elabE ctx receiver (some rt)
    let slot ← fresh rt
    let name := s!"$recursiveReceiver{slot}"
    ctx' := { ctx' with locals := { name, slot, ty := rt, mutable := false } :: ctx'.locals }
    pre := [.assign slot (← coerce receiver.pos r rt)]
    receiverArgs := [.ident p name]
  let tupleArg := pos[off]!
  let tt := Ty.tup (types.drop off |>.take (npos - off))
  let tuple ← coerce tupleArg.pos (← elabE ctx tupleArg (some tt)) tt
  let slot ← fresh tt
  let name := s!"$recursiveTuple{slot}"
  ctx' := { ctx' with locals := { name, slot, ty := tt, mutable := false } :: ctx'.locals }
  let parts := (List.range (npos - off)).map fun (i : Nat) =>
    SExpr.app tupleArg.pos (.ident tupleArg.pos name) [.int tupleArg.pos (i : Int)] false
  let packed ← elabGenericCallWith elabE ctx' p sig (receiverArgs ++ parts ++ args.filter isNamed)
    (some ty) (packArgs := true) (inst := inst)
  return ⟨(pre ++ [Expr.assign slot tuple]).foldr Expr.seq packed.e, packed.ty⟩

/-- Canonical arguments for a lazy producer edge. Calls already in
    positional form retain their lowering; tuple and named calls share
    the binding used by effectful first-success helpers. -/
def elabLoopArgsWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (p : Pos) (g : String)
    (args : List SExpr) (params : List Local) (slots : List Nat) (inst : List (String × Ty) := []) : EM Expr := do
  let named := args.any fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
  if let some sig := (ctx.sig? g).filter (fun s => !s.named.isEmpty || named || args.length != params.length) then
    let ty := Ty.tup (params.map (·.ty))
    let packed ← elabRecursiveArgsWith elabE ctx p sig args (params.map (·.ty)) inst
    let packet ← fresh ty
    let assign := (slots.zipIdx).foldr (fun (sl, j) acc =>
      Expr.seq (.assign sl (.prim (.tupGet j) [.local packet])) acc) (.lit .void)
    return .seq (.assign packet (← coerce p packed ty)) assign
  if args.length != params.length then
    eerr p s!"{g} takes {params.length} argument(s), found {args.length}"
  let es ← (args.zip params).mapM fun (a, l) => do
    let r ← elabE ctx a (some l.ty)
    coerce a.pos r l.ty
  return (es.zip slots).foldr (fun (e, sl) acc => .seq (.assign sl e) acc) (.lit .void)

partial def elabSetWith (elabE : Ctx → SExpr → Option Ty → EM R) (elabMember : Ctx → Pos → R → String → EM R)
    (ctx : Ctx) (p : Pos) (lhs0 : SExpr) (op : Option String) (rhs0 : SExpr) : EM R := do
  if let .app _ (.ident _ "$refineCopyOut") [rhs] false := rhs0 then
    let r ← elabSetWith elabE elabMember ctx p lhs0 op rhs
    match r.e with
    | .assign target (.local result) =>
      modify fun st => { st with frameCopies := st.frameCopies ++ [{ target, result }] }
    | .assign target (.prim (.tupGet field) [.local result]) =>
      modify fun st => { st with frameCopies := st.frameCopies ++ [{ target, result, field := some field }] }
    | _ => eerr p "internal error: a refining copy-out is not a saved result"
    return r
  -- (`$withOld(O, R)`: for `op=`, the old value was read into `O` before
  -- the code that computes `R`, as `set` evaluates, #208)
  let (rhs, oldIn) : SExpr × Option Expr := match rhs0 with
    | .app _ (.ident _ "$withOld") [.ident _ o, r] false => (r, (ctx.lookup o).map (fun l => Expr.local l.slot))
    | r => (r, none)
  -- the right side at the target's type; for `set F *= N` of a float, an
  -- int too (#127), so without it when that fails
  let rhsAt (t : Ty) : EM R :=
    if op == some "*" && t == .float then
      tryCatch (elabE ctx rhs (some t)) fun _ => elabE ctx rhs none
    else elabE ctx rhs (some t)
  -- in a method, a path from a field of `Self` (as when one is read)
  let rec selfRoot : SExpr → SExpr
    | .ident ip n =>
      match ctx.lookup n, ctx.selfClass with
      | none, some c => if (ctx.types.fields c).any (·.1 == n) then .member ip (.ident ip "Self") n else .ident ip n
      | _, _ => .ident ip n
    | .member sp e f => .member sp (selfRoot e) f
    | .app sp e [k] true => .app sp (selfRoot e) [k] true
    | .query sp e => .query sp (selfRoot e)
    | e => e
  let lhs := selfRoot lhs0
  let combine (old0 : Expr) (ty : Ty) (o : String) (new0 : R) : EM Expr := do
    let old := oldIn.getD old0
    -- (a refinement's value is its base; a refined variable is set only
    -- through a cast, #136)
    let new := widenR (← get).env new0
    if let .refine n := ty then
      eerr p s!"set {o}= on {withArticle n} needs a cast: write set X = {n}[X {o} …], which fails when the result is not one"
    match o, ty, new.ty with
    | "+", .int, .int => pure (p2 .add old new.e)
    | "-", .int, .int => pure (p2 .sub old new.e)
    | "*", .int, .int => pure (p2 .mul old new.e)
    | "+", .arr t, .arr u => do
        if t == u then pure (p2 .concat old new.e)
        else if refUp (← get).env (.arr u) (.arr t) then pure (p2 .concat old (← coerce p new (.arr t)))
        else if u.hasNever then
          match ← tryCatch (some <$> coerce p new (.arr t)) (fun _ => pure none) with
          | some e => pure (p2 .concat old e)
          | none => eerr p s!"cannot concatenate {ty.show} and {new.ty.show}"
        else eerr p s!"cannot concatenate {ty.show} and {new.ty.show}"
    -- floats (#127)
    | "+", .float, .float => pure (p2 .fadd old new.e)
    | "-", .float, .float => pure (p2 .fsub old new.e)
    | "*", .float, .float => pure (p2 .fmul old new.e)
    | "*", .float, .int => pure (p2 .fmul old (.prim .fofInt [new.e]))
    | "/", .float, .float => pure (p2 .fdiv old new.e)
    | "/", .int, _ => eerr p "set /= is not defined on int (integer division can fail)"
    | _, _, _ => eerr p s!"no operator '{o}=' for {ty.show} and {new.ty.show}"
  let mutableLocal (n : String) : EM Local := do
    match ctx.lookup n with
    | some l => if l.mutable then pure l else eerr p s!"'{n}' is not a var; declare it with var {n}:t = …"
    | none => eerr p s!"unknown variable '{n}'"
  -- a path `X.F[i]…`: the root variable and its steps (`some f` a field,
  -- `none` with an expression an index or key)
  let rec path : SExpr → Option (String × List (Pos × Option String × Option SExpr))
    | .ident _ n => some (n, [])
    | .member sp e f => (path e).map fun (n, ss) => (n, ss ++ [(sp, some f, none)])
    | .app sp e [k] true => (path e).map fun (n, ss) => (n, ss ++ [(sp, none, some k)])
    -- `X?`: the value inside an option; fails when empty
    | .query sp e => (path e).map fun (n, ss) => (n, ss ++ [(sp, some "?", none)])
    | _ => none
  let general : List (Pos × Option String × Option SExpr) → Bool
    | steps@(_ :: _ :: _) => !steps.isEmpty
    | steps => steps.any (·.2.1 == some "?")
  if let some (root, steps) := path lhs then if general steps then
    -- `set X.p = e` with a path of two or more steps (Book of Verse §3.5, §9.3):
    -- the indices and keys are evaluated once, left to right; then each
    -- intermediate container is read (an index or an intermediate key that
    -- is missing makes the set fail); then the new leaf; then the
    -- containers are rebuilt from the leaf up, ending with the variable
    -- the variable must be a var unless the path writes an object (below)
    let l ← match ctx.lookup root with
      | some l => pure l
      | none => eerr p s!"unknown variable '{root}'"
    let mut pre : Array Expr := #[]
    -- per step: the container's slot and type, and the step
    let mut levels : Array (Nat × Ty × Pos × Option String × Option (Nat × Ty)) := #[]
    let mut cur := l.slot
    let mut ty := l.ty
    -- first the indices and keys
    let mut keys : Array (Option (Nat × Ty)) := #[]
    let mut tys : Array Ty := #[]
    for (sp, f?, k?) in steps do
      tys := tys.push ty
      match f?, k?, ty with
      | some "?", _, .opt t => keys := keys.push none; ty := t
      | some "?", _, t => eerr sp s!"'?' in a set needs an option, found {t.show}"
      | some f, _, .struct sn targs =>
        match fieldIndex (ctx.types.fields sn targs) f with
        | some (_, ft) => keys := keys.push none; ty := ft
        | none => eerr sp s!"{ty.show} has no field '{f}'"
      | some f, _, t => eerr sp s!"{t.show} has no field '{f}'"
      | none, some k, .arr t =>
        let ri ← elabE ctx k (some .int)
        if ri.ty != .int then eerr sp "an array index must be an int"
        let ti ← fresh .int
        pre := pre.push (.assign ti ri.e)
        keys := keys.push (some (ti, .int)); ty := t
      | none, some k, .map kt vt =>
        let rk ← elabE ctx k (some kt)
        let tk ← fresh kt
        pre := pre.push (.assign tk (← coerce sp rk kt))
        keys := keys.push (some (tk, kt)); ty := vt
      | _, _, t => eerr sp s!"cannot index a value of type {t.show}"
    let leafTy := ty
    -- the last step from an object (#34): it writes the object in place, so
    -- the path above it is only read, and its field must be a var
    let tysA := tys
    let refLevel? : Option Nat := (List.range steps.length).reverse.find? fun k =>
      match tysA[k]! with
      | .struct sn _ => ctx.types.isRefClass sn
      | _ => false
    if let some kr := refLevel? then
      let (sp, f?, _) := steps.toArray[kr]!
      match tysA[kr]!, f? with
      | .struct sn _, some f =>
        if !ctx.types.isVarField sn f then eerr sp (classSetMsg sn f)
      | _, _ => eerr p "internal: set path"
    if refLevel?.isNone && !l.mutable then
      eerr p s!"'{root}' is not a var; declare it with var {root}:t = …"
    -- read one step of the container in slot `c` of type `cty`
    let readStep (c : Nat) (cty : Ty) (step : Option String) (key : Option (Nat × Ty)) : EM Expr := do
      match step, key, cty with
      | some "?", _, .opt _ => pure (.prim .query [.local c])
      | some f, _, .struct sn targs =>
        -- a class's field as when it is read (an interface field may sit at
        -- different places in different classes)
        if ctx.types.classes.contains sn then return (← elabMember ctx p ⟨.local c, cty⟩ f).e
        let (j, _) := (fieldIndex (ctx.types.fields sn targs) f).get!
        pure (.prim (.tupGet j) [.local c])
      | none, some (ti, _), .arr _ => pure (p2 .index (.local c) (.local ti))
      | none, some (tk, kt), .map _ vt =>
        let tp ← fresh (.tup [kt, vt])
        pure (mapLookup c tk tp)
      | _, _, _ => eerr p "internal: set path"
    -- a value of a class with no instance cannot exist, so the set is
    -- unreachable once the path reaches one; but the steps before it (the
    -- indices and keys, then the containers read) may fail first (#104)
    if let some ke := (List.range steps.length).find? fun k =>
        match tysA[k]! with | .struct sn _ => ctx.types.isEmptyClass sn | _ => false then
      let stepsA := steps.toArray
      let mut c := l.slot
      for k in [0:ke] do
        let (_, f?, _) := stepsA[k]!
        let c' ← fresh tysA[k + 1]!
        pre := pre.push (.assign c' (← readStep c tysA[k]! f? keys[k]!))
        c := c'
      -- (the right-hand side never runs, but is checked, and the field set
      -- at the empty class must be a var, as on any path)
      let lastCls := (List.range steps.length).reverse.find? fun k =>
        match tysA[k]!, stepsA[k]! with
        | .struct sn _, (_, some f, _) => f != "?" && ctx.types.classes.contains sn
        | _, _ => false
      if let some kc := lastCls then
        if let (.struct sn _, (sp, some f, _)) := (tysA[kc]!, stepsA[kc]!) then
          if !ctx.types.isVarField sn f then eerr sp (classSetMsg sn f)
      let r ← rhsAt leafTy
      match op with
      | none => discard <| coerce p r leafTy
      | some o => discard <| combine (.prim .userErr []) leafTy o r
      let tu ← fresh leafTy
      return ⟨pre.toList.foldr Expr.seq (.assign tu (.prim .userErr [])), leafTy⟩
    -- the intermediate containers: level 0 is a copy of the variable, taken
    -- after the indices, so that the right-hand side cannot change what is
    -- rebuilt (as for `set A[i] = e`); the variable is written once, last
    let c0 ← fresh l.ty
    pre := pre.push (.assign c0 (.local l.slot))
    cur := c0
    let stepsA := steps.toArray
    -- with an object on the path, the right-hand side runs once the path has
    -- reached it, before the values in the object are read (#34): a write it
    -- makes through the object is not lost. Without, it runs after every
    -- container is read, as for `set A[i] = e`.
    let rhsAfter : Nat := match refLevel? with
      | some kr => kr
      | none => stepsA.size
    let mut rhsVal : Option R := none
    let mut oldLeaf : Option Nat := none
    for k in [0:stepsA.size] do
      let (sp, f?, _) := stepsA[k]!
      levels := levels.push (cur, tys[k]!, sp, f?, keys[k]!)
      if k == rhsAfter then
        -- `set P op= e` reads P before e, as the direct form does (Book of
        -- Verse: `set X += e` is `set X = X + e`; #58): the rest of the path,
        -- read now, gives the old leaf (it fails as `P` would, and is read
        -- again for the rebuild below)
        if op.isSome then
          let mut c2 := cur
          for k2 in [k:stepsA.size] do
            let (_, f2, _) := stepsA[k2]!
            let t2 := if k2 + 1 < stepsA.size then tys[k2 + 1]! else leafTy
            let c3 ← fresh t2
            pre := pre.push (.assign c3 (← readStep c2 tys[k2]! f2 keys[k2]!))
            c2 := c3
          oldLeaf := some c2
        let r ← rhsAt leafTy
        let tr ← fresh r.ty
        pre := pre.push (.assign tr r.e)
        rhsVal := some ⟨.local tr, r.ty⟩
      if k + 1 < stepsA.size then
        let c ← fresh tys[k + 1]!
        pre := pre.push (.assign c (← readStep cur tys[k]! f? keys[k]!))
        cur := c
    let (lc, lty, _, lf, lkey) := levels[levels.size - 1]!
    -- a last `?` step also needs the option to be set
    if lf == some "?" then pre := pre.push (.seq (.prim .query [.local lc]) (.lit .void))
    -- the new leaf value
    let r ← match rhsVal with
      | some r => pure r
      | none => rhsAt leafTy
    let leaf ← match op with
      | none => coerce p r leafTy
      | some o =>
        -- (only an `op=` reads the old value: a read can have an effect)
        let old ← match oldLeaf with
          | some t => pure (Expr.local t)
          | none => readStep lc lty lf lkey
        combine old leafTy o r
    let tv ← fresh leafTy
    pre := pre.push (.assign tv leaf)
    -- rebuild, from the leaf up, as far as the object written in place
    let mut newVal : Expr := .local tv
    let mut wroteObject := false
    for k' in [0:levels.size] do
      let k := levels.size - 1 - k'
      if wroteObject then break
      let (c, cty, _, f?, key) := levels[k]!
      match f?, key, cty with
      | some "?", _, .opt _ => pre := pre.push (.assign c (.prim .mkSome [newVal]))
      | some f, _, .struct sn targs =>
        if ctx.types.isRefClass sn then
          let (j, ft) := (fieldIndex (ctx.types.fields sn targs) f).get!
          pre := pre.push (← setFieldAt ctx.types p sn targs c f j ft newVal)
          noteFx p ["writes"]
          wroteObject := true
        else
          let fs := ctx.types.fields sn targs
          let (j, _) := (fieldIndex fs f).get!
          let parts := (List.range fs.length).map fun i =>
            if i == j then newVal else Expr.prim (.tupGet i) [.local c]
          pre := pre.push (.assign c (.prim .mkTup parts))
      | none, some (ti, _), .arr _ =>
        pre := pre.push (.assign c (.prim .arrSet [.local c, .local ti, newVal]))
      | none, some (tk, _), .map _ vt =>
        -- the last key inserts or updates; an intermediate one was read above, so it exists
        let tvk ← fresh vt
        let ti ← fresh .int
        let tidx ← fresh .int
        pre := pre.push (.assign tvk newVal)
        pre := pre.push (mapPut c tk tvk ti tidx)
      | _, _, _ => eerr p "internal: set path"
      newVal := .local c
    if !wroteObject then pre := pre.push (.assign l.slot (.local c0))
    return ⟨pre.toList.foldr Expr.seq (.local tv), leafTy⟩
  match lhs with
  | .ident _ n =>
    let l ← mutableLocal n
    let r ← rhsAt l.ty
    let v ← match op with
      | none => coerce p r l.ty
      | some o => combine (.local l.slot) l.ty o r
    return ⟨.assign l.slot v, l.ty⟩
  | .app _ (.ident _ n) [k] true =>
    let l ← mutableLocal n
    match l.ty with
    | .map kt vt =>
      let rk ← elabE ctx k (some kt)
      let tk ← fresh kt
      let tp ← fresh (.tup [kt, vt])
      let r ← rhsAt vt
      let v ← match op with
        | none => coerce p r vt
        -- `set M[k] op= v` fails when k is not a key (Book of Verse §9.3)
        | some o => combine (mapLookup l.slot tk tp) vt o r
      let tv ← fresh vt
      let ti ← fresh .int
      let tidx ← fresh .int
      return ⟨.seq (.assign tk (← coerce p rk kt)) (.seq (.assign tv v)
        (.seq (mapPut l.slot tk tv ti tidx) (.local tv))), vt⟩
    | .arr t =>
      let i := k
      let ri := widenR ctx.types (← elabE ctx i (some .int))
      if ri.ty != .int then eerr p "an array index must be an int"
      let ti ← fresh .int
      let tv ← fresh t
      let r ← rhsAt t
      let v ← match op with
        | none => coerce p r t
        | some o => combine (p2 .index (.local l.slot) (.local ti)) t o r
      -- `set A[i] = v` fails out of range and returns `v` (Book of Verse §3.3)
      return ⟨.seq (.assign ti ri.e)
        (.seq (.assign l.slot (.prim .arrSet [.local l.slot, .local ti, .assign tv v])) (.local tv)), t⟩
    | ty => eerr p s!"cannot index a value of type {ty.show}"
  | .member _ (.ident _ n) f =>
    -- an object's field: written in place, through any variable (#34)
    if let some l := ctx.lookup n then
      if let .struct sn _ := l.ty then
        if ctx.types.isRefClass sn then
          let targs := match l.ty with | .struct _ ts => ts | _ => []
          let some (k, t) := fieldIndex (ctx.types.fields sn targs) f
            | eerr p s!"class {sn} has no field '{f}'"
          if !ctx.types.isVarField sn f then eerr p (classSetMsg sn f)
          let r ← rhsAt t
          noteFx p (if op.isSome then ["reads", "writes"] else ["writes"])
          let v ← match op with
            | none => coerce p r t
            -- (the current value, read as a read does)
            | some o => combine (← elabMember ctx p ⟨.local l.slot, l.ty⟩ f).e t o r
          return ⟨← setFieldAt ctx.types p sn targs l.slot f k t v, t⟩
    if let some l := ctx.lookup n then
      if let .struct sn targs := l.ty then
        if ctx.types.isEmptyClass sn then
          -- no instance can exist: unreachable
          let some (_, t) := fieldIndex (ctx.types.fields sn targs) f | eerr p s!"class {sn} has no field '{f}'"
          let tu ← fresh t
          return ⟨.assign tu (.prim .userErr []), t⟩
        if ctx.types.classes.contains sn && !ctx.types.isRefClass sn then
          eerr p s!"field '{f}' of the parametric class {sn} cannot be set: a parametric class is a value (#34)"
    let l ← mutableLocal n
    match l.ty with
    | .struct sn targs =>
      if ctx.types.classes.contains sn then eerr p (classSetMsg sn f)
      let fs := ctx.types.fields sn targs
      match fieldIndex fs f with
      | some (k, t) =>
        let r ← rhsAt t
        let v ← match op with
          | none => coerce p r t
          | some o => combine (.prim (.tupGet k) [.local l.slot]) t o r
        let tv ← fresh t
        -- the struct is rebuilt with field k replaced; `set` returns the new field value
        let parts := (List.range fs.length).map fun i =>
          if i == k then Expr.assign tv v else Expr.prim (.tupGet i) [.local l.slot]
        return ⟨.seq (.assign l.slot (.prim .mkTup parts)) (.local tv), t⟩
      | none => eerr p s!"struct {sn} has no field '{f}'"
    | ty => eerr p s!"{ty.show} has no field '{f}'"
  | _ => eerr p "openverse supports set X = …, and set on a path of fields, indices and keys from a variable (set S.F[i].G = …); not through a tuple element or a call result"

/-- `if (D := T[X]) then Body else Else`, where the cast holds only under a
    refinement of the code's type parameters (#243). `Body` is lifted into
    a generic function (`Refine.functions`), asked for in a first
    elaboration, which elaborates `Body` in the refined world to find its
    type, effects and the locals it uses. Then the `if` is a dispatch to
    it, one test per set of pins among the classes tested, as a refined
    method call is: `Typed.dispatch` types the call under the refinement,
    with the object (as `D`) and those locals passed at their refined
    types. `none` when the cast does not refine: the plain path. -/
partial def elabRefinedIfWith (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (elabE : Ctx → SExpr → Option Ty → EM R) (withMark : Ctx → Expr → EM Expr) (ctx : Ctx) (p _dp : Pos) (D T : String) (x : SExpr) (body0 : SExpr)
    (elseE : Option SExpr) (exp : Option Ty) (made : Bool := false)
    (escRet : Option (Ty × Refine.Exits) := none)
    (outsideWrites : List Nat := []) :
    EM (Option R) := do
  let env := ctx.types
  if !env.classes.contains T then return none
  -- (in a method: the members of `Self` the branch names bare, as members
  -- of `Self`, which its function takes as a parameter)
  let body := match ctx.selfClass with
    | some c => selfQualify ctx c body0
    | none => body0
  let st0 ← get
  let rx ← elabE { ctx with canFail := true, inTaking := true } x none
  let some (S, sargs, targs, common, eqs, opened) := refiningCast? env T rx.ty (env.tvars.map (·.1))
    | do set st0; return none
  if !env.isRefClass S || (!opened.isEmpty && !env.isRefClass T) then set st0; return none
  -- (#250: `T` has Verse Core type arguments past the object's, or not as
  -- its own type parameters: its tests open them, as a method's dispatch does)
  let wide := !((env.coreVars T).length == (env.coreArgs S sargs).length &&
    (env.coreVars T).all fun (v, _) => !v.startsWith "$arg")
  let coreFields (n : String) (ts : List Ty) : Option (List Ty) :=
    if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
  let some (μT, opened) := castRefinement? env eqs opened (env.comparableArgs T targs) | do set st0; return none
  let targs := targs.map fun t => t.subst (opened.filterMap fun (n, _, c) => if c then some (n, Ty.param n true) else none)
  let shown := (Ty.struct T targs).show
  -- (the locals the branch uses, in order of first use)
  let caps : List Local := (Choice.namesUsed body).filterMap fun n =>
    if n == D then none else ctx.locals.find? (·.name == n)
  -- (the `var`s from outside it that the branch sets, its `return`s and its
  -- `break`s that leave it, `refineExits`: copies in the branch, and its
  -- function returns what they say, which the caller does after the `if`;
  -- not again for the branch made so, whose `return`s are its function's,
  -- `escRet`)
  let setOut := caps.filter fun l => l.mutable && (Refine.findPart (fun
      | .set _ lhs _ _ => Choice.rootName? lhs == some l.name
      | _ => false) false body).isSome
  if let some (q, what) := refineBranchWhy? ctx p body ((caps.filter (·.mutable)).map (·.name) |>.filter fun n => !setOut.any (·.name == n))
      (allowEsc := true) then
    eerr q s!"the branch of the cast to {shown}, which holds only under a refinement of the type arguments, is compiled as a function of its own, so {what} (#243)"
  let retPart := Refine.findPart (fun | .ret .. => true | _ => false) false body
  let brkPart := Refine.findPart Refine.isBreak true body
  let escapes := retPart.isSome || brkPart.isSome
  if escRet.isNone && (!setOut.isEmpty || escapes) then
    -- (the `if`'s value: by its type where it is; with none there, the
    -- `else`'s, found apart, `void` carrying nothing)
    let vm? : Option ExitVal ← match elseE, exp with
      | none, _ => pure (some .none)
      | some _, some .void => pure (some .none)
      | some _, some t => pure (some (if escapes then .opt t.toSTy else .raw (some t.toSTy)))
      | some ee, none =>
        if escapes && escapesAlways (Choice.stmtsOf body) then pure (some .elseAfter)
        else do
          let st ← get
          let τ? ← tryCatch (do pure (some (← elabE { ctx with typeOnly := true } ee none).ty)) fun _ => pure none
          set st
          if !escapes then
            -- Discard a statement's value before building the copy-out tuple.
            pure (some (if τ?.any (· == .void) then .none else .raw none))
          else
            pure (τ?.map fun τ => if τ == .void then ExitVal.none else .opt τ.toSTy)
    let some vm := vm?
      | eerr ((retPart.orElse fun _ => brkPart).map (·.pos) |>.getD p) s!"the branch of the cast to {shown}, which holds only under a refinement of the type arguments, is compiled as a function of its own, so it cannot return or break out of it yet where the if's value is used at a type not known there (write it) (#243)"
    let sourceRet ← match ctx.refineExits.ret with
      | some (some (_, t), _) => resolveTy env p t
      | some (none, _) => pure .void
      | none => match ctx.forReturnSlot.bind ctx.lookup with
        | some { ty := .opt t, .. } => pure t
        | _ => pure ctx.retTy
    let retS := if sourceRet == .void then none else some sourceRet.toSTy
    let (thenB, elseB, tupS, t, after, exits) := refineExits p body0 elseE (setOut.map fun l => (l.name, l.ty.toSTy))
      retPart.isSome brkPart retS vm
    set st0
    let tupTy ← tupS.mapM (resolveTy env p ·)
    -- (the new branch is the elaborator's, so its function is made from it,
    -- `made`, not from the source)
    let some rIf ← elabRefinedIfWith elabApp elabE withMark ctx p _dp D T x thenB (some elseB) tupTy (made := true)
        (escRet := if escapes then tupTy.map (·, exits) else none) (outsideWrites := outsideWrites ++ setOut.map (·.slot))
      | eerr p s!"internal: the cast to {shown} with sets, returns or breaks in its branch (#243)"
    let slot ← fresh rIf.ty
    let c := { ctx with locals := { name := t, slot, ty := rIf.ty, mutable := false } :: ctx.locals }
    let rest ← elabE c (.block p after) exp
    return some ⟨.seq (.assign slot rIf.e) rest.e, rest.ty⟩
  -- (a suspension in the branch makes its function `<suspends>`, whose
  -- dispatch the lowering takes as a suspends method's call, #243; the
  -- `else` is the caller's code, which may suspend as any)
  let isS (f : Nat) : Bool := ctx.sigs.any fun s => s.idx == f && s.suspends
  let immediateLifts := env.castRequests.filter (!·.waits) |>.map (·.name)
  -- Cancellation itself is immediate. Keep scanning its receiver.
  let mayWait (f : Nat) : Bool :=
    ctx.sigs.any fun s => s.idx == f && s.suspends && s.name != "$cancelMark" && !immediateLifts.contains s.name
  let startsTask (f : Nat) : Bool :=
    ctx.sigs.any fun s => s.idx == f && (s.name == "$spawnMark" || s.name == "$branchMark")
  let waits (e : Expr) : Bool := Suspend.countSusp mayWait (fun _ => false) false startsTask e > 0
  let elseOf : EM R := match elseE with
    | none => pure ⟨.lit .void, .void⟩
    | some ee => elabE ctx ee exp
  let tag := refineTagOf ctx
  let key := Refine.keyOf p D tag
  let liftName := s!"$refine{p.line}_{p.col}_{D}" ++ (if p.file.isEmpty then "" else s!"_{p.file}") ++ tag
  -- Keep a suspending lift's available parameters in a stable order from
  -- discovery onward: locals it declares may themselves be borrowed by a
  -- nested lift, whose frame reference needs exactly this argument order.
  let availableTypes : List Ty := env.tvars.map (fun binding => Ty.subst μT binding.2) ++
    opened.map (fun binding => Ty.param binding.1 binding.2.2)
  let available := Ty.mergeParamBounds (availableTypes.flatMap Ty.paramsC)
  match env.castRequests.find? (·.key == key) with
  | none =>
    -- (first: the branch in the refined world)
    let refine (t : Ty) : Ty := t.subst μT
    let dTy := refine (.struct T targs)
    let dslot ← fresh dTy
    let ctxB : Ctx := { ctx with
      locals := { name := D, slot := dslot, ty := dTy, mutable := false } ::
        ctx.locals.map fun l => { l with ty := refine l.ty, storage := l.storage.map (·.subst μT) },
      frameName := liftName, frameArgs := available.map fun (n, c) => Ty.param n c,
      -- (the source return's value and the lifted function's copy-out)
      retTy := (escRet.map (refine ·.1)).getD ctx.retTy,
      refineExits := (escRet.map (·.2)).getD {},
      defers := if escRet.isSome then [] else ctx.defers,
      -- (and the type arguments the cast opens, #250)
      types := { env with tvars := (env.tvars.map (fun (n, t) => (n, refine t)) ++
        opened.map (fun (n, _, c) => (n, Ty.param n c))) } }
    -- (its own effects, which its function declares; the enclosing one's too)
    let fx0 := (← get).fx
    let pending0 := (← get).pendingSuspendingCasts
    let waiting0 := (← get).pendingWaitingCasts
    let source0 := (← get).pendingSourceSuspends
    let background := (← get).backgroundSlots
    modify fun st => { st with fx := [] }
    let retarget (h : ConstructHint) : ConstructHint :=
      if h.frame == ctx.frameName then { h with frame := liftName } else h
    let ctxB := { ctxB with constructHints := ctxB.constructHints.map (·.map retarget) }
    let body := pruneConstructHints ctxB liftName
      (pruneConstructHints { ctxB with frameName := ctx.frameName } liftName body)
    let rb ← elabE ctxB body (if elseE.isNone then some .void else exp.map refine)
    let waitingThen := (← get).pendingWaitingCasts
    let thenWaits := ctx.suspends && (waitingThen != waiting0 || waits rb.e)
    let sourceSuspends := ctx.suspends && ((← get).pendingSourceSuspends != source0 || ctx.sourceWaits rb.e)
    if thenWaits then
      for l in caps do
        if l.mutable && l.storage.isNone && (background.contains l.slot || outsideWrites.contains l.slot) then
          eerr p s!"internal error: a suspending mutable capture '{Choice.shownName l.name}' has no source storage"
    let fxB := (← get).fx
    modify fun st => { st with fx := fx0 }
    for (k, q, via) in fxB do noteFx q [k] via
    let re ← elseOf
    -- Preserve the dispatch shape when lowering either side. Task starts
    -- need lowering too, but only a wait exposes copies of shared slots.
    let hasPending := (← get).pendingSuspendingCasts != pending0
    let needsFrame (f : Nat) := isS f || ctx.sigs.any (fun s => s.idx == f && s.name == "$branchMark")
    let suspendsB := ctx.suspends && (hasPending || Suspend.hasSusp needsFrame rb.e || Suspend.hasSusp needsFrame re.e)
    let elseWaits := ctx.suspends && ((← get).pendingWaitingCasts != waitingThen || waits re.e)
    let τ' : Ty := if elseE.isNone then .void else exp.getD re.ty
    let ret := refine τ'
    discard <| coerce p rb ret
    let decides := rb.e.mayFail ctx.sigProg
    let sig := caps.map fun l => (l.name, refine l.ty)
    let tps := Ty.mergeParamBounds ((dTy :: ret :: sig.map (·.2)).flatMap Ty.paramsC)
    -- (the type parameters only the types written in the branch mention:
    -- each through a parameter of its own, passed a value of it, so that
    -- the call determines it)
    let written := ((Refine.typeNames body).filterMap fun w =>
      (env.tvars.lookup w).map refine).flatMap Ty.paramsC
    let storage := caps.filterMap fun l => l.storage.map fun s =>
      (l.name, s.subst μT)
    let storageTypes := (storage.flatMap (fun (_, s) => s.args)).flatMap Ty.paramsC
    let wanted := (if ctx.suspends then available else []) ++ storageTypes ++ written
    let allTps := Ty.mergeParamBounds (tps ++ wanted)
    let extra := allTps.filter fun (n, _) => !tps.any (·.1 == n)
    let tps := Ty.mergeParamBounds (if ctx.suspends then available ++ allTps else allTps)
    -- (the opened ones' values come from the object's hidden fields; those
    -- of a cast this one is in, from its function's, #250)
    if let some (n, _) := tps.find? fun (n, _) =>
        !ctx.dictVars.contains n && !opened.any (·.1 == n) && !ctx.types.tvars.any (·.1 == n) then
      eerr p s!"cannot lift the branch of the cast to {shown} yet: its types mention {n}, which this function has no value of (#243)"
    -- (from the enclosing function's own names, also through the
    -- refinements of the casts this one is in, as the branch is taken from
    -- the source)
    let σ := env.tvars.filterMap fun (n, t) =>
      let t' := refine t
      match t' with
      | .param m _ => if m == n then none else some (n, t'.toSTy)
      | _ => some (n, t'.toSTy)
    let heap := ["reads", "writes", "allocates"].filter fun k => fxB.any (·.1 == k)
    let specs := (if heap.isEmpty then ["computes"] else heap) ++ (if decides then ["decides"] else []) ++
      (if suspendsB then ["suspends"] else [])
    let lift : Refine.Lift := {
      pos := p, bound := D, target := T, tag, continuationScope := ctx.refineScope,
      name := liftName,
      params := ((D, dTy) :: sig).map (fun (n, t) => { name := n, ty := t.toSTy }) ++
        extra.map fun (n, _) => { name := s!"$type{n}", ty := .name n },
      tparams := tps.map fun (n, c) => { pos := p, name := n, constraint := if c then "comparable" else "type" },
      specs, ret := ret.toSTy, subst := σ, opened := opened.map fun (n, v, _) => (n, v), waits := thenWaits, sourceSuspends,
      exits := Refine.Exits.substTypes ((escRet.map (·.2)).getD {}) σ,
      storage := storage.map fun (n, s) => (n, { frame := s.frame, name := s.name, args := s.args.map Ty.toSTy }),
      inRepeat := ctx.inRepeat, sourceContext := sourceContextOf ctx, liftTag := some ctx.liftTag,
      inlineScopes := ctx.inlineScopes,
      -- (made: a branch the elaborator made, for a cast with clauses
      -- after it, #286, which the source does not have as such)
      -- (and a tagged one, which the source's places do not find, #53)
      body := if ctx.selfClass.isSome || made || D.startsWith "$" || !tag.isEmpty then some (pruneConstructHints ctxB liftName
        (pruneConstructHints { ctxB with frameName := ctx.frameName } liftName body)) else none }
    modify fun st => if st.castNeeds.any (·.key == key) then st else { st with castNeeds := st.castNeeds ++ [lift] }
    if suspendsB then
      modify fun st => { st with pendingSuspendingCasts := st.pendingSuspendingCasts + 1 }
    if thenWaits || elseWaits then
      modify fun st => { st with pendingWaitingCasts := st.pendingWaitingCasts + 1 }
    if sourceSuspends || ctx.sourceWaits re.e then
      modify fun st => { st with pendingSourceSuspends := st.pendingSourceSuspends + 1 }
    -- (a placeholder: this elaboration goes no further)
    return some ⟨if decides then .prim .fail [] else .prim .userErr [], τ'⟩
  | some l =>
    -- (then: the object in a slot, and one dispatch per set of pins)
    let (pre, y) ← match rx.e with
      | .local y => pure ([], y)
      | e => do
        let y ← fresh rx.ty
        pure ([Expr.assign y e], y)
    let re ← elseOf
    let τ' : Ty := if elseE.isNone then .void else exp.getD re.ty
    let eE ← coerce p re τ'
    let rargs := env.coreArgs S sargs
    let atR := rargs.zipIdx.map fun (r, j) => (pinArg j, r)
    let needOf (pins : List (Option Ty)) := (rargs.zip pins).filterMap fun (a, pin) => match pin with
      | some pt => let pt := pt.subst atR; if a == pt then none else some (a, pt)
      | none => none
    let mut parts : Array (List (Option Ty) × Array String) := #[]
    -- (keyed by each class's pins on the object's type arguments: the
    -- branch needs none of those a class below adds, so a test of classes
    -- that share those pins opens what the fewest of them add, as the
    -- checker's `openCount` does: none when one of them adds none; a cast
    -- that opens type arguments, #250, by all of each class's pins, as a
    -- method's dispatch is, since its tests open them)
    for d in common do
      -- (#351: through views, one test per class, each with its view and
      -- all of its pins, which the view relates to the object's)
      if env.viewed.contains S then parts := parts.push (env.corePins d, #[d]) else
      let k := if wide then env.dispatchPins d else (env.dispatchPins d).take rargs.length
      match parts.findIdx? (·.1 == k) with
      | some pi => parts := parts.modify pi fun (k', ds) => (k', ds.push d)
      | none => parts := parts.push (k, #[d])
    -- (an object that is no local: evaluated with a test of all the
    -- classes tested, in one condition, so that its effects roll back and
    -- its failure takes the else when the cast fails; the dispatch then
    -- tests each part, its end unreachable)
    let mut acc := if pre.isEmpty then eE else .prim .userErr []
    let mut tested : Array String := #[]
    for (pins, part) in parts.toList.reverse do
      -- (#250: the type arguments the test opens, as fresh parameters
      -- `$ext i`, which the refinement binds; the object is a `T` at the
      -- first of them)
      -- (each as comparable as the parameter it stands for: the target's,
      -- or past those, the tested class's own)
      -- (#351: through views, the object's are all fresh, as many as the
      -- class has, related to `X`'s by its view)
      let viewedS := env.viewed.contains S
      let dV := part[0]!
      let nV := (env.coreVars dV).length
      let extOf : List Ty := if viewedS then (List.range nV).map fun i => Ty.param s!"$ext{i}" false
        else if !wide then [] else
        (List.range (pins.length - rargs.length)).map fun i => Ty.param s!"$ext{i}" false
      let rxs := if viewedS then extOf else rargs ++ extOf
      let atX := rxs.zipIdx.map fun (r, j) => (pinArg j, r)
      let viewEqs : List (Ty × Ty) := if !viewedS then [] else rargs.zip (env.viewOf S dV extOf)
      let needX : List (Ty × Ty) := viewEqs ++ (rxs.zip pins).filterMap fun (a, pin) => match pin with
        | some pt => let pt := pt.subst atX; if a == pt then none else some (a, pt)
        | none => none
      if !VTy.pinsBelow (env.lowerPins pins) rxs.length then
        eerr p s!"cannot cast {withArticle rx.ty.show} to {shown} yet: class {part[0]!} relates its type arguments to ones that {S} does not have (#209, #243)"
      -- (no object of `part` can be this one: no test)
      let some μF := Ty.unifyEqs coreFields [] (if wide || viewedS then needX else needOf pins) | continue
      -- (the object as a `T`: its type parameters from the test's type
      -- arguments, refined)
      let dTyX ← if !wide && !viewedS then pure ((Ty.struct T targs).subst μF) else
        -- (a target seen through views has the tested class's view of it, #351)
        let rxsF := rxs.map (·.subst μF)
        match Ty.unifyEqs coreFields [] ((env.coreArgs T targs).zip
            (if env.viewed.contains T then env.viewOf T dV rxsF else rxsF)) with
        | some θD => pure ((Ty.struct T targs).subst θD)
        | none => eerr p s!"cannot cast {withArticle rx.ty.show} to {shown} yet: the object's type arguments as {withArticle part[0]!} do not determine {T}'s (#250)"
      let targetArgs := match dTyX with | .struct _ args => args | _ => []
      let some μF := env.refineComparable? μF (env.comparableArgs T targetArgs) | continue
      let dTyX := dTyX.subst μF
      let dL : Local := { name := D, slot := y, ty := dTyX, mutable := false }
      -- As for method dispatch, pass witnesses at the caller's own types.
      -- Pins may equate one to a newly opened component of a compound type.
      let unrefine := μF.filterMap fun (x, t) =>
        if ctx.dictVars.contains x && t.params.any (·.startsWith "$ext") then
          (ctx.types.tvars.lookup x).map (t, ·)
        else none
      let ctx' := { ctx with
        unrefine := unrefine ++ ctx.unrefine,
        locals := dL :: ctx.locals.map fun loc => { loc with ty := loc.ty.subst μF, storage := loc.storage.map (·.subst μF) },
        types := { env with tvars := env.tvars.map fun (m, t) => (m, t.subst μF) } }
      let argOf (sp : SParam) : SExpr :=
        if sp.name.startsWith "$type" then .app p (.ident p "$witness") [.ident p (sp.name.drop 5).toString] false
        else .ident p sp.name
      let rc ← elabApp ctx' p (.ident p l.name) (l.params.map argOf)
        (l.specs.contains "decides") (some (τ'.subst μF))
      -- (a suspends call carries the defers active at it, which go around
      -- the whole dispatch instead, as a method's, #243)
      let rcE : Expr := match rc.e with
        | .seq (.ite (.prim .fail []) _ (.lit .void)) b => b
        | e => e
      let .call fi (.local s0 :: es) := rcE
        | eerr p s!"cannot lift the branch of the cast to {shown} yet: its call is not a plain one (#243)"
      if s0 != y then eerr p s!"cannot lift the branch of the cast to {shown} yet (#243)"
      acc := .ite (.heap (.isTag (part.toList.map env.tagOf)) [.local y]) (.call fi (.local y :: es)) acc
      tested := part ++ tested
    let t ← fresh τ'
    -- (its value in a temporary at its type, as a suspends call's takes,
    -- and the defers active here around it when its function suspends)
    let mark (e : Expr) : EM Expr := if l.specs.contains "suspends" then withMark ctx e else pure e
    if pre.isEmpty then return some ⟨← mark (.assign t acc), τ'⟩
    let cond := pre.foldr Expr.seq (.heap (.isTag (tested.toList.map env.tagOf)) [.local y])
    return some ⟨← mark (.assign t (.ite cond acc eE)), τ'⟩

/-- Infer a producer's signature instance from its canonical arguments. -/
def loopInstanceOf (ctx : Ctx) (p : Pos) (sig : Sig) (types : List Ty) : EM (List (String × Ty)) := do
  let some σ := (sig.params.zip types).foldlM (fun σ (pt, t) => Ty.matchArg ctx.types σ pt t) []
    | eerr p s!"cannot infer the parameter instance of {sig.name}'s lazy generator (#283)"
  if let some (n, _) := sig.tparams.find? fun (n, _) => (σ.lookup n).isNone then
    eerr p s!"{sig.name}'s type parameter {n} is not determined by its arguments' types here (#235)"
  return σ

/-- Resolve a mutual member's private source aliases while keeping actual
    Core parameter names at their own identities, including permutations. -/
def loopMemberCtx (ctx : Ctx) (entry member : String) (σ : List (String × Ty)) : Ctx :=
  if entry == member then ctx else
  let aliases := σ.map fun (n, t) => (Choice.memberTypeName member n, t)
  let core := Ty.mergeParamBounds (σ.flatMap fun (_, t) => t.paramsC)
  let tvars := aliases ++ core.map (fun (n, cmp) => (n, Ty.param n cmp)) ++ ctx.types.tvars
  { ctx with types := { ctx.types with tvars } }

/-- A lazy invocation selects one leaf after running its path's prefixes.
    Leaf contexts retain branch bindings for saved continuation items. -/
structure LoopTailCode where
  select : Expr
  arms : Array (Ctx × List SExpr)
  itemCode : Expr
  next : Nat

partial def elabLoopTailWith (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx))
    (ctx : Ctx) (tail : SExpr) (k start : Nat) : EM LoopTailCode := do
  let vd : Expr := .lit .void
  let c := { ctx with canFail := true, inTaking := true }
  match tail with
  | .app _ (.ident _ "$returnTail") [.block p ss] false =>
    let (pre, value) := Choice.loopBlockParts p ss
    let (r, ca) ← elabSeq c pre none
    let code ← elabLoopTailWith elabSeq ca value k start
    return { code with select := .seq r.e code.select, itemCode := .seq r.e code.itemCode }
  | .ite _ cs t (some u) =>
    let (cond, ca) ← elabSeq c cs none
    let yes ← elabLoopTailWith elabSeq ca t k start
    let no ← elabLoopTailWith elabSeq ctx u k yes.next
    return { select := .ite cond.e yes.select no.select, arms := (yes.arms ++ no.arms),
             itemCode := .seq cond.e (.seq yes.itemCode no.itemCode), next := no.next }
  | value =>
    let alts := (Choice.alts? value).getD [value]
    return { select := .seq (.assign k (.lit (.int (start : Nat)))) vd,
             arms := #[(ctx, alts)], itemCode := vd, next := start + alts.length }

/-- (#283) `elabLoopGen` for a strongly connected group of functions with
    several values, taken lazily (`$group(tail, $member(H, params, clauses,
    r := tail)…)` in the marker): one stack of items `(k, every member's
    parameters and names…)`, `k` the alternative to run, numbered across
    the members, or `-1 - i` to start member `i` (its clauses, then its
    branch). A call of a member, `$rec` (its own) or `$recTo(H, …)`, pushes
    the item that starts that member, its parameters from the arguments.
    Otherwise as `elabLoopGen`. Defined before the mutual block, with the
    block's functions it calls as arguments (#325). -/
partial def elabLoopGenGroupWith (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx))
    (ctx : Ctx) (p : Pos) (g : String) (ps cls : List SExpr) (_rsty : STy) (tail0 : SExpr)
    (members : List SExpr) : EM LoopGen := do
  let vd : Expr := .lit .void
  let args ← ps.mapM fun
    | .ident q n => match ctx.lookup n with
      | some l => pure l
      | none => eerr q s!"internal: parameter {n} of a $loop (#246)"
    | e => eerr e.pos "internal: a $loop parameter (#246)"
  let some entry := ctx.sig? g | eerr p s!"internal: no signature for {g} (#283)"
  let σ ← loopInstanceOf ctx p entry (args.map (·.ty))
  let rty := entry.ret.subst σ
  let templates ← members.mapM fun
    | .app _ (.ident _ "$member") [.ident _ h, .block _ hps, .block _ hcls, .decl _ _ _ _ htail] false =>
      pure (h, hps, hcls, htail)
    | _ => eerr p "internal: a $member (#283)"
  let templates := (g, ps, cls, tail0) :: templates
  let mut instances := [(g, σ)]
  for (h, _, _, _) in templates.drop 1 do
    if let some sig := (ctx.sig? h).filter (·.tparams.isEmpty) then
      instances := instances ++ [(sig.name, [])]
  -- Discover each generic member at the actual calls reaching it. This
  -- uses ordinary tuple/named/default binding and result-type inference,
  -- in an isolated probe whose slots, effects and helper requests are reset.
  -- Later edges are checked against the established instance when lowered,
  -- just as self-recursive lazy calls keep their invocation's parameter types.
  if instances.length < templates.length then
    let mut todo := instances.map (·.1)
    let mut errors : List (String × String) := []
    while !todo.isEmpty do
      let h := todo.head!
      todo := todo.tail!
      let some (_, hps, hcls, htail) := templates.find? (·.1 == h)
        | eerr p "internal: a mutual generator template"
      let some sig := ctx.sig? h | eerr p s!"internal: no signature for {h} (#283)"
      let saved ← get
      let ts := sig.params.map (·.subst ((instances.lookup h).getD []))
      let pls ← (hps.zip ts).mapM fun
        | (.ident _ n, t) => do return ({ name := n, slot := ← fresh t, ty := t, mutable := false } : Local)
        | _ => eerr p "internal: a $member parameter (#283)"
      let c := loopMemberCtx ctx g h ((instances.lookup h).getD [])
      let c := { c with locals := pls.reverse ++ c.locals, typeOnly := true, canFail := true, inTaking := true }
      let (_, cc) ← elabSeq c hcls none
      let probeK ← fresh .int
      let code ← elabLoopTailWith elabSeq cc htail probeK 0
      for (ca, alts) in code.arms do
        for alt in alts do
          let call := match alt with
            | .app q (.ident _ "$rec") as false => some (q, h, as)
            | .app q (.ident _ "$recTo") (.ident _ target :: as) false => some (q, target, as)
            | _ => none
          if let some (q, target, as) := call then
            if (instances.lookup target).isSome then continue
            let some targetSig := ctx.sig? target | eerr q s!"internal: no signature for {target} (#283)"
            let attempt ← tryCatch (do
              let packet ← elabE { ca with callInstanceProbe := some target }
                (.app q (.ident q target) as targetSig.decides) (some rty)
              let .tup types := packet.ty | eerr q "internal: a mutual argument type packet"
              pure (Except.ok ((targetSig.tparams.map (·.1)).zip types))) (fun err => pure (.error err))
            match attempt with
            | .ok σ =>
              instances := instances ++ [(target, σ)]
              todo := todo ++ [target]
            | .error err => errors := errors ++ [(target, err)]
      restoreConstructProbe ctx saved
    for (h, _, _, _) in templates do
      if (instances.lookup h).isNone then
        throw ((errors.lookup h).getD s!"cannot infer {h}'s mutual generator instance (#283)")
  -- (the members: the called one first, its parameters' slots its own)
  let mut ms : Array (String × List Local × List SExpr × SExpr) := #[]
  let pls0 ← args.mapM fun l => do return { l with slot := ← fresh l.ty }
  ms := ms.push (g, pls0, cls, tail0)
  for m in members do
    let .app _ (.ident _ "$member") [.ident _ h, .block _ hps, .block _ hcls, .decl _ _ _ _ htail] false := m
      | eerr p "internal: a $member (#283)"
    let some sig := ctx.sig? h | eerr p s!"internal: no signature for {h} (#283)"
    if hps.length != sig.params.length then eerr p s!"internal: the parameters of {h} (#283)"
    let hpls ← (hps.zip (sig.params.map (·.subst ((instances.lookup h).getD [])))).mapM fun (e, t) => match e with
      | .ident _ n => do return ({ name := n, slot := ← fresh t, ty := t, mutable := false } : Local)
      | _ => eerr p "internal: a $member parameter (#283)"
    ms := ms.push (h, hpls, hcls, htail)
  let names := ms.toList.map (·.1)
  -- (each member's clauses, then its branches' conditions, in its own
  -- context; the names each saves in an item: its parameters, then the others)
  let k ← fresh .int
  let mut infos : Array (R × LoopTailCode × List Local) := #[]
  for (h, pls, mcls, mtail) in ms do
    let c := loopMemberCtx ctx g h ((instances.lookup h).getD [])
    let lctx : Ctx := { c with locals := pls.reverse ++ c.locals }
    let newOf (c : Ctx) : List Local := c.locals.take (c.locals.length - lctx.locals.length)
    let (rc, cc) ← elabSeq { lctx with canFail := true, inTaking := true } mcls none
    let code ← elabLoopTailWith elabSeq cc mtail k 0
    let mut tls : List Local := pls
    for l in (newOf cc ++ code.arms.toList.flatMap fun (ca, _) => newOf ca).reverse do
      if !tls.any (·.slot == l.slot) then tls := tls ++ [l]
    infos := infos.push (rc, code, tls)
  -- (one item for all: every member's names, the members in order)
  let all : List Local := infos.toList.flatMap (·.2.2)
  let bases : List Nat := (infos.toList.foldl (fun (acc, n) (_, _, tls) => (acc ++ [n], n + tls.length)) ([], 0)).1
  let tupTy : Ty := .tup (.int :: all.map (·.ty))
  let cellTy : Ty := .struct "$lazycell" [tupTy]
  let cfs := ctx.types.fields "$lazycell" [tupTy]
  let (some (itemF, _), some (nextF, _)) := (fieldIndex cfs "$LItem", fieldIndex cfs "$LNext")
    | eerr p "internal: the stack cells of a $loop (#246)"
  let w ← fresh (.opt cellTy)
  let cell ← fresh cellTy
  let sp ← fresh .int
  let it ← fresh tupTy
  let has ← fresh .logic
  let nx ← fresh .int
  let item (kE : Expr) (vals : List Expr) : Expr := .prim .mkTup (kE :: vals)
  let cur : List Expr := all.map (Expr.local ·.slot)
  let push (e : Expr) : Expr :=
    .seq (.assign cell (.heap (.new (ctx.types.tagOf "$lazycell")) [e, .local w]))
      (.seq (.assign w (.prim .mkSome [.local cell]))
        (.seq (.assign sp (p2 .add (.local sp) (.lit (.int 1)))) vd))
  -- (the item that starts member `j`, its parameters from `ts`)
  let startOf (j : Nat) (ts : List Nat) : Expr :=
    let b := bases.getD j 0
    item (.lit (.int (-1 - (j : Int)))) (cur.take b ++ ts.map Expr.local ++ cur.drop (b + ts.length))
  -- (the alternatives, numbered across the members' branches)
  let mut offs : Array Nat := #[]
  let mut total : Nat := 0
  for (_, armCode, _) in infos do
    offs := offs.push total
    total := total + armCode.next
  let mut alts : Array Expr := #[]
  let mut values : Array (Nat × Expr) := #[]
  let mut itemCode : Expr := vd
  let mut argSet : Option Pos := none
  let mut starts : Array Expr := #[]
  for ((rc, armCode, _), i) in infos.toList.zipIdx do
    let off := offs.getD i 0
    itemCode := .seq itemCode (.seq rc.e armCode.itemCode)
    let firsts : List Nat := (armCode.arms.toList.foldl (fun (acc, n) (_, as) => (acc ++ [n], n + as.length)) ([], off)).1
    let select := .seq armCode.select (.assign k (p2 .add (.local k) (.lit (.int (off : Nat)))))
    starts := starts.push (.ite (.seq rc.e select) vd (.seq (.assign k (.lit (.int (total : Nat)))) vd))
    for ((ca, as), first) in armCode.arms.toList.zip firsts do
      for (a, j) in as.zipIdx do
        let gi := first + j
        let actx : Ctx := { ca with canFail := true, inTaking := true }
        let next? : Option Nat := if j + 1 < as.length then some (gi + 1) else none
        let cont : Expr := match next? with
          | some n => push (item (.lit (.int (n : Nat))) cur)
          | none => vd
        let call? : Option (Nat × List SExpr × Pos) := match a with
          | .app q (.ident _ "$rec") args' false => some (i, args', q)
          | .app q (.ident _ "$recTo") (.ident _ h :: args') false => (names.idxOf? h).map (·, args', q)
          | _ => none
        match call? with
        | some (jm, args', q) =>
          let some (h, hpls, _, _) := ms[jm]? | eerr q "internal: a call in a group (#283)"
          if argSet.isNone then
            argSet := args'.findSome? fun a' =>
              if Choice.anyE (fun | .set .. => true | _ => false) a' then some a'.pos else none
          let ts ← hpls.mapM fun l => fresh l.ty
          let assigns ← elabLoopArgsWith elabE actx q h args' hpls ts ((instances.lookup h).getD [])
          itemCode := .seq itemCode assigns
          alts := alts.push (.ite assigns (.seq cont (push (startOf jm ts))) cont)
        | none =>
          let r ← elabE actx a (some rty)
          values := values.push (gi, ← coerce a.pos r rty)
          let nextK : Int := match next? with | some n => (n : Int) | none => -1
          alts := alts.push (.seq (.assign nx (.lit (.int nextK))) (.seq (.assign has (.lit (.logic true))) vd))
  let dispatch : Expr := (alts.toList.zipIdx).foldr (fun (a, i) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) a acc) vd
  let unpack : Expr := (all.zipIdx).foldr (fun (l, j) acc =>
    .seq (.assign l.slot (.prim (.tupGet (j + 1)) [.local it])) acc) vd
  let init : Expr := .seq (.assign w (.lit .none)) (.seq (.assign sp (.lit (.int 0)))
    (push (item (.lit (.int (-1))) (args.map (Expr.local ·.slot) ++ cur.drop pls0.length))))
  let start : Expr := (starts.toList.zipIdx).foldr (fun (st, i) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (-1 - (i : Int))))) st acc) vd
  let step : Expr := Expr.seq (.assign sp (p2 .sub (.local sp) (.lit (.int 1))))
    (.seq (.ite (.assign cell (.prim .query [.local w]))
        (.seq (.assign it (.heap (.get itemF) [.local cell])) (.seq (.assign w (.heap (.get nextF) [.local cell])) vd)) vd)
    (.seq (.assign k (.prim (.tupGet 0) [.local it]))
    (.seq unpack
    (.seq (.assign has (.lit (.logic false)))
    (.seq (.ite (p2 .lt (.local k) (.lit (.int 0))) start vd)
      dispatch)))))
  let value : Expr := values.toList.foldr (fun (i, e) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) e acc) (.prim .fail [])
  let after : Expr := .ite (p2 .ge (.local nx) (.lit (.int 0))) (push (item (.local nx) cur)) vd
  return { init, step, sp, has, value, after, vty := rty, itemCode, argSet, instances }

/-- (#283) A body for the elaboration that chooses overloads: each
    `$inlineOv(F, id, call, …)` its call as written, `$ovPick(id, F, call)`. -/
partial def ovForTypes : SExpr → SExpr :=
  Choice.mapE fun
    | .app p (.ident _ "$inlineOv") (.ident q f :: .int _ id :: call :: _) false =>
      some (.app p (.ident p "$ovPick") [.int p id, .ident q f, ovForTypes call] false)
    | _ => none

/-- (#283) The body with each `$inlineOv` its chosen overload's inlined
    call, `picks` the overload (`F$ovK`) each id's call took. -/
partial def ovChosen (picks : List (Nat × String)) : SExpr → SExpr :=
  Choice.mapE fun
    | .app p (.ident _ "$inlineOv") (.ident q f :: .int _ id :: _ :: cands) false =>
      let k? : Option Nat := (picks.lookup id.toNat).bind fun o => ((o.splitOn "$ov").getLast?).bind (·.toNat?)
      match k?.bind (cands[·]?) with
      | some c => some (ovChosen picks c)
      | none => some (.app p (.ident p "$ovUnresolved") [.ident q f] false)
    | _ => none

/-- Check a construction's value choices at the field's expected type.
    Keeping the original inline/lazy templates visits nested constructions
    under their real parameter aliases, rather than replacing them by calls. -/
def constructFieldsForTypes : SExpr → SExpr
  | .decl p f t v x =>
    .decl p f t v (if Choice.hasLiftable x then
      .app x.pos (.ident x.pos "$constructValuesType") [x] false else x)
  | e => e

set_option maxHeartbeats 800000 in
mutual
partial def elabE (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  if !ctx.constructProbe && ctx.constructHints.isNone &&
      Choice.anyE (fun
        | e@(.construct _ n [] _) =>
          !((ctx.types.sparams.lookup n).getD []).isEmpty && Choice.hasLiftable e
        | _ => false) se then
    let st0 ← get
    discard <| elabE { ctx with constructProbe := true, typeOnly := true, constructOrigin := some ctx.frameName } se exp
    let hints := (← get).constructHints
    set st0
    return ← elabE { ctx with constructHints := some hints, constructOrigin := some ctx.frameName } se exp
  match se with
  | .app _ (.ident _ "$spawnResult") [call] false => elabE ctx call none
  | .app p (.ident _ "$spawnBound") (.ident _ fname :: .ident _ adapter :: args) false =>
    elabSpawnBound ctx p fname adapter args
  | .app _ (.ident _ "$defaultContext") [.block _ stack, .int _ flags, call] false =>
    let defaults := stack.filterMap fun
      | .tuple _ [.str _ [.text f], .str _ [.text n]] => some (f, n)
      | _ => none
    elabE { ctx with defaults := defaults ++ ctx.defaults, inRepeat := flags % 2 == 1, inDefer := flags / 2 % 2 == 1, inDefaultCheck := flags / 4 % 2 == 1 } call exp
  | .app _ (.ident _ "$sourceSuper")
      [.str _ [.text c], .str _ [.text method], .ident _ receiver, call] false => do
    let some self := ctx.lookup receiver | eerr se.pos "internal: missing source method receiver"
    let cctx := { ctx with locals := { self with name := "Self" } :: ctx.locals }
    elabE { cctx with selfClass := some c, selfMethod := if method.isEmpty then none else some method } call exp
  | .app _ (.ident _ "$methodMiss") [] false => pure ⟨.prim .fail [], .never⟩
  | .app p (.ident _ "$allValues") [.block _ cs, value] false =>
    elabE ctx (.forE p (Choice.gensOf "" cs (choiceOrder ctx)) value) exp
  | .app _ (.ident _ "$methodCast") [cast] false => elabE ctx cast exp
  | .app _ (.ident _ "$methodCase") [cast] false => elabE ctx cast exp
  | .app p (.ident _ "$constructProbe") [.str _ [.text site], .construct q n ts fs] false =>
    let r ← elabConstruct ctx q n ts (fs.map constructFieldsForTypes) exp
    modify fun st => { st with constructHints := constructHint ctx q n site r.ty :: st.constructHints }
    return r
  | .app p (.ident _ "$constructValuesType") [value] false =>
    let name := s!"$constructValue{p.line}_{p.col}"
    let (r, c) ← elabOneClauses { ctx with canFail := true, inTaking := true }
      [.decl p name (exp.map Ty.toSTy) false value]
    let some valueLocal := c.lookup name | eerr p "construction type probe did not bind its value"
    return ⟨.seq r.e (.local valueLocal.slot), valueLocal.ty⟩
  | .app p (.ident _ "$fieldDefault")
      [.str _ [.text site], .str _ [.text origin], .app _ (.ident _ "$constructHints") [.block _ hints] false,
       .construct q n ts [], .ident _ f] false =>
    let ty ← constructInstance ctx q n ts site origin hints
    let tas := match ty with | .struct _ tas => tas | _ => []
    let some (_, t, some d) := (ctx.types.fields n tas).find? (·.1 == f)
      | eerr p s!"field '{f}' of {n} has no default value"
    return ⟨← elabFieldDefault ctx p n tas f t d, t⟩
  | .app p (.ident _ "$fieldValue")
      [.str _ [.text site], .str _ [.text origin], .app _ (.ident _ "$constructHints") [.block _ hints] false,
       .construct q n ts [], .ident _ f, value] false =>
    let ty ← constructInstance ctx q n ts site origin hints
    let tas := match ty with | .struct _ tas => tas | _ => []
    let some (_, t, _) := (ctx.types.fields n tas).find? (·.1 == f)
      | eerr p s!"struct {n} has no field '{f}'"
    return ⟨← coerce p (← elabE ctx value (some t)) t, t⟩
  | .int p n =>
    if !Int64.inRange n then eerr p s!"integer literal {n} does not fit in 64 bits"
    return litAt ctx.types exp ⟨.lit (Value.ofInt n), .int⟩
  | .char _ c => return ⟨.lit (.char c), .char⟩
  | .char32 _ c => return ⟨.lit (Value.ofInt c), .char32⟩
  | .float _ b => return litAt ctx.types exp ⟨.lit (.float b), .float⟩
  | .str p parts =>
    let pieces ← parts.mapM fun part => match part with
      | .text s => pure (Expr.lit (Value.ofString s))
      | .code e => do toStringOf e.pos (← elabE ctx e none)
    let _ := p
    match pieces with
    | [] => return ⟨.lit (Value.ofString ""), Ty.string⟩
    | e :: es => return ⟨es.foldl (fun a b => p2 .concat a b) e, Ty.string⟩
  -- (#209) a hidden field's default: a value of its type
  | .ident p "$witness" =>
    match exp with
    | some t => return ⟨← witness ctx.types ctx.dictBase ctx.dictVars t, t⟩
    | none => eerr p "internal error: a witness without a type"
  | .ident p n =>
    match n with
    | "true" => return ⟨.lit (.logic true), .logic⟩
    | "false" =>
      match exp with
      | some (.opt t) => return ⟨.lit .none, .opt t⟩
      | some (.arr t) => return ⟨.lit Value.emptyArray, .arr t⟩
      | some .void => return ⟨.lit .void, .void⟩
      | _ => return ⟨.lit (.logic false), .logic⟩
    | _ =>
      match ctx.lookup n with
      | some l => return ⟨.local l.slot, l.ty⟩
      | none =>
        -- in a method, a field of `Self`
        if let some c := ctx.selfClass then
          if (ctx.types.fields c).any (·.1 == n) then
            return ← elabE ctx (.member p (.ident p "Self") n) exp
          if ctx.hasMethod c n ||
              ((ctx.types.methodOverloads.lookup n).map (·.any (ctx.hasMethod c ·))).getD false then
            -- (a method of `Self` as a value, #210, also an overloaded one,
            -- which the member says is no value)
            return ← elabE ctx (.member p (.ident p "Self") n) exp
        match ctx.sig? n with
        | some s =>
          -- (#214) a function wanted at a closed function type of its arity
          -- that no class of its gives, not asked for yet: asked for, as a
          -- placeholder, the program is elaborated again with a class made
          -- for it (if the function fits the type)
          let askFor : Option Ty := match exp with
            | some t@(.struct m ts) =>
              match FnValues.parseName m with
              | some (k, _) =>
                let _ := k
                if (ts.all fun u => u.params.isEmpty) &&
                    !ctx.types.fnRequests.contains (n, t) && fnFits ctx.types s t then some t else none
              | none => none
            | _ => none
          if s.isConst then
            noteFx p s.fx (some s!"uses the constant {n}")
            return ⟨.call s.idx [], s.ret⟩
          else if let some (cls, ty) := (do
              -- (#214) a value class made for the function type expected,
              -- a written closed one the function fits other than at its
              -- own types (by variance, or a generic one at an instance)
              let t@(.struct m _) ← exp | none
              if (FnValues.parseName m).isNone then none
              let env := ctx.types
              let c ← env.classes.find? fun (c : String) => c.startsWith s!"{n}$fn$" &&
                let i := (env.info c).ifaces.headD ""
                Ty.struct i ((env.iargs.lookup (c, i)).getD []) == t
              some (c, t) : Option (String × Ty)) then
            let r ← elabE ctx (.construct p cls [] []) none
            return ⟨← coerce p r ty, ty⟩
          else if !s.tparams.isEmpty then
            if let some ty := exp then
              if let .struct shape _ := ty then
                if let some (k, _) := FnValues.parseName shape then
                  for cls in [s!"{n}$fn", s!"{n}$fnPack", s!"{n}$fnUnpack{k}"] do
                    let some args := fnClassArgs ctx.types cls ty | continue
                    let r ← elabConstruct ctx p cls [] [] (some (.struct cls args))
                    return ⟨← coerce p r ty, ty⟩
            if let some t := askFor then
              modify fun st => { st with fnNeeds := st.fnNeeds ++ [(n, t)] }
              return ⟨.prim .userErr [], t⟩
            eerr p s!"'{n}' is generic: a function type determining all its type arguments and satisfying its bounds must be expected (#214, #209)"
          else if ctx.types.classes.contains s!"{n}$fn" then
            -- a function as a value (#210): its class's object, of the
            -- function type expected, else of its own
            let sh : FnValues.Shape := ⟨s.params.length, s.decides, s.suspends, s.fx⟩
            let own : Ty := .struct sh.name (s.params ++ [s.ret])
            let ty := match exp with
              | some t@(.struct m _) => if (FnValues.parseName m).isSome then t else own
              | _ => own
            -- (through its own type; when the expected one does not fit, as
            -- its own, which the caller then joins or names in a mismatch)
            let r ← elabE ctx (.construct p s!"{n}$fn" [] []) none
            let r : R := ⟨← coerce p r own, own⟩
            if ty == own then return r
            match ← tryCatch (some <$> coerce p r ty) (fun _ => pure none) with
            | some e => return ⟨e, ty⟩
            | none =>
              if let some t := askFor then
                modify fun st => { st with fnNeeds := st.fnNeeds ++ [(n, t)] }
                return ⟨.prim .userErr [], t⟩
              return r
          else if let some t := askFor then
            modify fun st => { st with fnNeeds := st.fnNeeds ++ [(n, t)] }
            return ⟨.prim .userErr [], t⟩
          else if !s.named.isEmpty then
            eerr p s!"'{n}' has named parameters: such a function cannot be used as a value (a function type has no named parameters)"
          else eerr p s!"'{n}' is a function: call it with {n}(…)"
        | none =>
          if (ctx.types.overloads.lookup n).isSome then
            eerr p s!"{n} is overloaded: an overloaded function cannot be used as a value (Book of Verse ch. 6)"
          -- the float constants (#132), unless the program defines them
          match n with
          | "PiFloat" => return ⟨.lit (.float (VFloat.canon 3.141592653589793)), .float⟩
          | "Inf" => return ⟨.lit (.float 0x7FF0000000000000), .float⟩
          | "NaN" => return ⟨.lit (.float VFloat.nanBits), .float⟩
          | _ => eerr p s!"unknown identifier '{Choice.shownName n}'"
  -- a constructor's `block:` (#11): it cannot fail, as a class's cannot
  | .app _ (.ident _ "$nofail") [e] false => elabE { ctx with canFail := false, inBlock := true } e exp
  | .app p (.ident _ "$defer") _ _ => eerr p "defer: is a statement: it has no value"
  | .app p (.ident _ "$sync") arms false => elabConc ctx p true arms exp
  | .app p (.ident _ "$race") arms false => elabConc ctx p false arms exp
  | .app p (.ident _ "$rush") arms false => elabConc ctx p false arms exp true
  | .app p (.ident _ "$spawn") [body] false => elabSpawn ctx p body
  | .app p (.ident _ "$branch") [body] false => elabBranch ctx p body
  | .app p (.ident _ "$refineBreak") [] false =>
    if ctx.inChoice then
      eerr p "break cannot leave the clauses of a failure context that has a choice (an if condition, first{…}, option{…}, …) (#208)"
    match ctx.refineExits.brk with
    | some pack =>
      if ctx.inDefer then eerr p "break cannot leave a defer: block"
      elabRefineExit ctx p [] pack
    | none => elabE ctx (.brk p) exp
  | .app _ (.ident _ "$witness") [.ident _ n] false =>
    -- (a value of type parameter `n`, as the hidden argument of a generic
    -- call for it: the type argument of a lifted branch (#243) that only its
    -- written types mention)
    let t := (ctx.types.tvars.lookup n).getD (.param n false)
    return ⟨← witness ctx.types ctx.dictBase ctx.dictVars t, t⟩
  | .app p (.ident _ "$stageWitness") [.decl _ _ (some ty) _ _] false => do
    let ty ← resolveTy ctx.types p ty
    return ⟨← witness ctx.types ctx.dictBase ctx.dictVars ty, ty⟩
  | .app p (.ident _ "$fxOf") [.ident _ f] false =>
    -- (an inlined call of a function with several values: its declared
    -- effects, as at a call, #235)
    if let some s := ctx.sig? f then noteFx p s.fx (some s!"calls {Choice.shownFnName f}")
    return ⟨.lit .void, .void⟩
  -- (a continuation's body, #335: clauses lifted already, failing where their
  -- first filter does, then the values)
  | .app p (.ident _ "$forFirst") [.block _ clauses, body] false => elabFor ctx p clauses body (prepared := true) (firstDecides := true)
  | .app _ (.ident _ "$forEnvCapture") [value] false => do
    let fx := (← get).fx
    let r ← elabE ctx value exp
    modify fun st => { st with fx }
    return r
  | .app p (.ident _ "$forStageFlatten") [value] false => do
    let r ← elabE ctx value none
    match r.ty with
    | .arr (.arr t) => return ⟨.prim .flatten [r.e], .arr t⟩
    | .opt (.arr (.arr t)) =>
      let result ← fresh r.ty
      let slot ← fresh (.arr (.arr t))
      return ⟨.seq (.assign result r.e) (.ite (.assign slot (.prim .query [.local result]))
        (.prim .mkSome [.prim .flatten [.local slot]]) (.lit .none)), .opt (.arr t)⟩
    | _ => eerr p "internal: staged flatten values"
  | .app p (.ident _ "$forPrepare") [.str _ [.text base], .decl _ _ (some view) _ _, .block _ copyIds, .block _ borrowIds, .ident _ flat, .block _ clauses, body] false => do
    let some plan := ctx.types.loopRequests.findSome? (fun l => l.stagePlan.filter (·.base == base))
      | eerr p "internal: missing for prepare plan"
    let .struct _ args ← resolveTy ctx.types p view | eerr p "internal: for prepare view"
    let copyNames := forStageCopyNames copyIds
    let borrowNames := borrowIds.filterMap fun | .ident _ n => some n | _ => none
    let req ← match forStagePrefixOf ctx plan args p clauses body (flat == "true") copyNames borrowNames with
      | .ok req => pure req
      | .error why => eerr p s!"cannot prepare this refining for: {why} (#417)"
    if !ctx.types.loopRequests.any (·.key == req.key) then
      modify fun st => { st with loopFirst := st.loopFirst ++
        [{ g := "", pos := p, itemCode := .lit .void, argSet := none, lift := .ok req }] }
      let ty ← resolveTy ctx.types p req.ret
      return ⟨.prim .userErr [], ty⟩
    elabApp ctx p (.ident p req.name) req.args true exp
  | .app p (.ident _ "$forStage") [.str _ [.text base], .decl _ _ (some view) _ _, .block _ copyIds, .block _ borrowIds, .ident _ root, .ident _ flat, .block _ clauses, body] false => do
    let some plan := (ctx.forStage.filter (·.base == base)).orElse fun _ =>
        ctx.types.loopRequests.findSome? (fun l => l.stagePlan.filter (·.base == base))
      | eerr p "internal: missing for stage plan"
    let .struct _ args ← resolveTy ctx.types p view | eerr p "internal: for stage view"
    let copyNames := forStageCopyNames copyIds
    let borrowNames := borrowIds.filterMap fun | .ident _ n => some n | _ => none
    let outcome := root == "true" && plan.outcome
    let failed : SExpr := if plan.copies.isEmpty then .ident p "false" else
      .tuple p (.ident p "false" :: copyNames.map (SExpr.ident p ·))
    let r ← elabFor { ctx with
      forStage := some plan, forStageArgs := args, forStageFlat := flat == "true", forStageCopies := copyNames, forStageBorrows := borrowNames,
      forExitPacket := if outcome then some failed else ctx.forExitPacket } p clauses body
      (prepared := true) (firstDecides := true)
    if !outcome then return r
    return ⟨.prim .mkSome [r.e], .opt r.ty⟩
  | .app p (.ident _ "$forResumeValues") [envs, .block _ copyIds, .block _ _] false => do
    let copyNames := forStageCopyNames copyIds
    let input ← elabE ctx envs none
    let r ← match input.ty with
      | .opt (.arr _) => forOutcomeValues ctx p input
      | _ => pure input
    let .arr (.struct base _) := r.ty | eerr p "internal: for resume environments"
    let some plan := ctx.types.loopRequests.findSome? (fun l => l.stagePlan.filter (·.base == base))
      | eerr p "internal: missing for resume plan"
    let slot ← fresh r.ty
    let source := s!"{base}$ready"
    let env := source ++ "$env"
    let packet := source ++ "$packet"
    let c := { ctx with forStage := none, locals := { name := source, slot, ty := r.ty, mutable := false } :: ctx.locals }
    let call := SExpr.app p (.member p (.ident p env) plan.method) [] false
    let body := if plan.copies.isEmpty then call else
      let get (j : Nat) := SExpr.app p (.ident p packet) [.int p (j : Int)] false
      SExpr.block p (.decl p packet none false call ::
        (copyNames.zipIdx.map fun (n, j) => .set p (.ident p n) none
          (.app p (.ident p "$refineCopyOut") [get (j + 1)] false)) ++ [get 0])
    let body := if plan.outcome then .app p (.ident p "$forOutcomeValues") [body] false else body
    -- Preparation never executes a real generator: each successful prefix
    -- supplies exactly one environment. Dispatch directly, retaining the
    -- enclosing outcome target across this suspending call.
    let first := SExpr.app p (.ident p source) [.int p 0] true
    let values ← elabE c (.ite p [.decl p env none false first] body
      (some (.app p (.ident p "Err") [] false))) none
    let .arr _ := values.ty | eerr p "internal: for resume values"
    return ⟨.seq (.assign slot r.e) values.e, values.ty⟩
  | .app p (.ident _ "$forFirstOutcome") [.block _ clauses, body, failed] false => do
    let flag ← fresh .logic
    let r ← elabFor { ctx with forOutcomeSlot := some flag, forExitPacket := some failed } p clauses body
      (prepared := true) (firstDecides := true) (failure := some failed)
    let result ← fresh (.opt r.ty)
    return ⟨.seq (.assign flag (.lit (.logic true)))
      (.seq (.assign result (.lit .none))
        (.seq (.loop (.seq (.assign result (.prim .mkSome [r.e])) Expr.brkV))
          (.ite (.prim .query [.local flag]) (.local result) (.lit .none)))), .opt r.ty⟩
  | .app p (.ident _ "$forOutcomeValues") [value] false => do
    forOutcomeValues ctx p (← elabE ctx value none)
  | .app _ (.ident _ "$forReturns") [_, .ident _ mode, body] false =>
    elabE { ctx with canFail := mode == "true" } body exp
  | .app _ (.ident _ "$forReturnBody") [.set _ (.ident _ slot) none _, .ident _ mode, body] false =>
    elabE { ctx with canFail := mode == "true", defers := [], forReturnSlot := some slot } body exp
  | .app _ (.ident _ "$forReturnBody") [.block _ [.set _ (.ident _ slot) none _, _], .ident _ mode, body] false =>
    elabE { ctx with canFail := mode == "true", defers := [], forReturnSlot := some slot } body exp
  | .app _ (.ident _ "$forClauseExits") [.set _ (.ident _ slot) none _, .set _ (.ident _ breaking) none _, .ident _ mode, body] false =>
    elabE { ctx with
      canFail := mode == "true", defers := [], forReturnSlot := some slot,
      forBreakCapture := some breaking, forBreakSlot := none, inLoop := true, loopDefers := 0 } body exp
  -- (#283) a call of an overloaded function with several values, as
  -- written, in the elaboration for types: the overload it takes noted
  | .app _ (.ident _ "$ovPick") [.int _ id, .ident _ f, call] false =>
    elabE { ctx with ovPick := some (id.toNat, f) } call exp
  | .app p (.ident _ "$inlineOv") (.ident _ f :: _) false =>
    eerr p s!"a call of {Choice.shownFnName f}, which is overloaded and has several values, is supported in the body of a function or method only, for now (#283)"
  | .app p (.ident _ "$ovUnresolved") [.ident _ f] false =>
    eerr p s!"internal: which overload of {Choice.shownFnName f} this call takes (#283)"
  -- (#283, `Choice.bifToExcl`) a block as an `if`'s branch binding a name
  -- its condition binds
  | .app _ (.ident _ "$shadows") [.ident q n] false =>
    eerr q s!"'{n}' is already defined; Verse does not allow shadowing (use set {n} = … for a var)"
  | .app p (.ident _ "$inline") (.ident _ f :: _) false =>
    if ctx.inTaking then
      if ctx.liftWhy != "" then
        eerr p s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from {ctx.liftWhy}, for now (#283)"
      eerr p (s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from here, for now (#235): " ++
        "not from a defer:'s body, " ++
        "an alternative of a set's choice, the right of " ++
        "and or or, a range, or a block with a range of its own as a branch")
    eerr p (s!"{Choice.shownFnName f} has several values, so a call of it must be in a failure context that takes them: " ++
      "an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#235)")
  | .app p (.ident _ "$each") (.app _ (.ident _ fa) _ _ :: _) false =>
    -- (a call of a recursive function with several values, #235)
    let f := if fa.endsWith "$all" then String.ofList (fa.toList.take (fa.length - 4)) else fa
    if ctx.inTaking then
      if ctx.liftWhy != "" then
        eerr p s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from {ctx.liftWhy}, for now (#283)"
      eerr p (s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from here, for now (#235): " ++
        "not from a defer:'s body, " ++
        "an alternative of a set's choice, the right of " ++
        "and or or, a range, or a block with a range of its own as a branch")
    eerr p (s!"{Choice.shownFnName f} has several values, so a call of it must be in a failure context that takes them: " ++
      "an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#235)")
  | .app p (.ident _ "$loop") (.ident _ f :: _) false =>
    -- (a call of a recursive function with several values taken lazily, #246)
    if ctx.inTaking then
      if ctx.liftWhy != "" then
        eerr p s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from {ctx.liftWhy}, for now (#283)"
      eerr p (s!"a call of {Choice.shownFnName f}, which has several values, cannot be lifted from here, for now (#235): " ++
        "not from a defer:'s body, " ++
        "an alternative of a set's choice, the right of " ++
        "and or or, a range, or a block with a range of its own as a branch")
    eerr p (s!"{Choice.shownFnName f} has several values, so a call of it must be in a failure context that takes them: " ++
      "an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#235)")
  | .app p (.ident _ "$choice") _ false =>
    if ctx.inTaking && ctx.liftWhy != "" then
      eerr p s!"a choice (a | b) cannot be lifted from {ctx.liftWhy}, for now (#283)"
    if ctx.inTaking then
      eerr p ("a choice (a | b) cannot be lifted from here, for now (#208): not from a defer:'s body, " ++
        "an alternative of a set's " ++
        "choice, the right of and or or, a range, or a block with a range of its own as a branch")
    eerr p ("a choice (a | b) has several values, so it must be in a failure context that takes them: " ++
      "an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#208)")
  | .app p (.ident _ "$callArgs") [.ident _ g, .block _ args] false =>
    let some sig := ctx.sig? g | eerr p s!"internal: no signature for {g}'s arguments"
    if let some (.tup types) := exp then
      return ← elabRecursiveArgsWith elabE ctx p sig args types
    elabGenericCallWith elabE ctx p sig args exp (packArgs := true)
  | .app p (.ident _ "$callArgs") [.ident _ g, .block _ args, .block _ types] false =>
    let some sig := ctx.sig? g | eerr p s!"internal: no signature for {g}'s arguments"
    let inst ← types.mapM fun
      | .decl q n (some t) _ _ => do pure (n, ← resolveTy ctx.types q t)
      | _ => eerr p "internal: a recursive call's type instance"
    if let some (.tup types) := exp then
      return ← elabRecursiveArgsWith elabE ctx p sig args types inst
    elabGenericCallWith elabE ctx p sig args exp (packArgs := true) (inst := inst)
  | .app p (.ident _ "$paramDefault") [.ident _ f, .ident _ n, .block _ earlier, d] false =>
    -- (#283) the default of a named parameter an inlined call of a function
    -- with several values omits: in the context a call gives it (the
    -- parameters before it, under their own names; no return; failing only
    -- for a <decides> function)
    let some s := ctx.sig? f | eerr p s!"internal: no signature for {f} (#283)"
    let locals : List Local := earlier.filterMap fun
      | .tuple _ [.ident _ orig, .ident _ t] => (ctx.lookup t).map fun l => { l with name := orig }
      | _ => none
    let key := (s.name, s!"?{n}")
    if ctx.defaults.contains key then
      eerr p s!"the default of ?{n} of {f} uses itself (a call of {f} that omits ?{n})"
    let dctx := { ctx with locals := locals.reverse, selfClass := none, inParamDefault := true,
                           inLoop := false, canFail := ctx.canFail && s.decides,
                           suspends := ctx.suspends && s.suspends, defaults := key :: ctx.defaults }
    let rd ← fxAt p (elabE dctx d exp)
    if !s.decides && rd.e.mayFail ctx.sigProg then
      eerr p s!"the default of ?{n} of {f} can fail, but {f} is not <decides>"
    return rd
  | .app _ (.ident _ "$noLift") [.str _ [.text why], e] false =>
    -- (#283) a block or construction kept: elaborated as it is, its choice
    -- refused with why
    elabE { ctx with liftWhy := why } e exp
  | .app p (.ident _ "$firstP") [.block _ items] false =>
    -- (#246) `first{…}` of clauses that are lifted already (a consumer's,
    -- taken into a lazily taken call's function of its own): not again,
    -- which would bind their lifted names a second time
    let (code, c1) ← elabOneGo { ctx with inLoop := false, inChoice := ctx.inLoop, inTaking := true, canFail := true }
      items.dropLast
    let c1 := { c1 with inLoop := ctx.inLoop, inChoice := ctx.inChoice, inTaking := ctx.inTaking, canFail := ctx.canFail }
    let rv ← elabE c1 (items.getLastD (.tuple p [])) exp
    return ⟨.seq (Expr.firstE code) rv.e, rv.ty⟩
  | .app p (.ident _ "$first") [.block bp items] false =>
    -- `first{…}` and `first(…){…}`: without a choice, a block
    if !Choice.hasChoice items.dropLast (choiceOrder ctx) then return ← elabE ctx (.block bp items) exp
    -- with one (#208): the first success of the clauses, then the value (or
    -- body), which sees their names
    if !ctx.canFail then
      eerr p "first{…} with a choice can fail, but it is not in a failure context (#208)"
    let (rc, c1) ← elabOneClauses ctx items.dropLast
    let rv ← elabE c1 (items.getLastD (.tuple p [])) exp
    return ⟨.seq rc.e rv.e, rv.ty⟩
  | .app p f args bracket => elabApp ctx p f args bracket exp
  | .member p (.ident _ n) m =>
    if n == "(super:)" then
      eerr p s!"(super:){m} cannot be used as a value: call it with (super:){m}(…), or name a method that calls it"
    match ctx.lookup n, ctx.types.enums.lookup n with
    | none, some vals =>
      -- `color.Red`: an enumerator
      match vals.idxOf? m with
      | some k => return ⟨.lit (Value.ofInt k), .enum n⟩
      | none => eerr p s!"enum {n} has no value '{m}'"
    | _, _ => elabMember ctx p (← elabE ctx (.ident p n) none) m exp
  | .member p e m => elabMember ctx p (← elabE ctx e none) m exp
  | .construct p name targs args => elabConstruct ctx p name targs args exp
  | .mapLit p entries => elabMapLit ctx p entries exp
  | .structDef p _ _ | .enumDef p _ _ | .refineDef p _ _ _ => eerr p "struct, enum and type definitions must be at the top level"
  | .query p e =>
    let r ← elabE ctx e none
    match r.ty with
    | .opt t => return ⟨.prim .query [r.e], t⟩
    | .logic => return ⟨.prim .query [r.e], .logic⟩
    | t => eerr p s!"'?' needs an option or logic, found {t.show}"
  | .neg p e =>
    -- (the expected type, a float or an int, as a hint: `-Id(2.5)`)
    let hint : Option Ty := match exp with
      | some .float => some .float
      | _ => none
    let r0 ← elabE ctx e hint
    let r := widenR ctx.types r0
    -- (the negation of a refined value is of an expected refinement whose
    -- interval holds the flipped one, #143)
    if let (.refine n, some (.refine m)) := (r0.ty, exp) then
      if let (some (bn, cn), some (bm, cm)) := (ctx.types.refines.lookup n, ctx.types.refines.lookup m) then
        if bn == bm && intervalWithin (intervalNeg (refineInterval cn)) (refineInterval cm) then
          return ⟨.prim (if bn == .float then .fneg else .neg) [r.e], .refine m⟩
    if r.ty == .float then return litAt ctx.types exp ⟨.prim .fneg [r.e], .float⟩
    if r.ty != .int then eerr p s!"unary '-' needs an int or a float, found {r.ty.show}"
    return litAt ctx.types exp ⟨.prim .neg [r.e], .int⟩
  | .notE _ e =>
    -- (with a choice, its first success, #208)
    let e := (Choice.takeFirst? e (choiceOrder ctx)).getD e
    let r ← elabE { ctx with canFail := true, inTaking := true } e none
    return ⟨Expr.notE r.e, .void⟩
  | .bin p "/" a b =>
    -- `X / Y` on ints: a rational, failing when `Y = 0` (#116)
    let ra := widenR ctx.types (← elabE ctx a none)
    let rb := widenR ctx.types (← elabE ctx b (if ra.ty == .float then some .float else none))
    -- (on floats, IEEE division: by zero an infinity or NaN, #127)
    if ra.ty == .float && rb.ty == .float then return ⟨p2 .fdiv ra.e rb.e, .float⟩
    if ra.ty == .float || rb.ty == .float then
      eerr p s!"no operator '/' for {ra.ty.show} and {rb.ty.show} (an int is not a float: write X * 1.0)"
    if ra.ty == .rational || rb.ty == .rational then
      eerr p "'/' divides ints: openverse has no arithmetic on rationals (only Floor, Ceil and comparisons)"
    let es := [← coerce a.pos ra .int, ← coerce b.pos rb .int]
    return ⟨← ratCall ctx p "$ratMake" es, .rational⟩
  | .bin p op a b =>
    let ra := widenR ctx.types (← elabE ctx a none)
    let rb ← match op, ra.ty with
      | "+", .arr _ =>
        -- (an array of other classes, to join, #67)
        if ctx.retries ≥ 3 then elabE ctx b (some ra.ty)
        else
          let c2 := { ctx with retries := ctx.retries + 1 }
          tryCatch (elabE c2 b (some ra.ty)) fun _ => elabE c2 b none
      | "*", .int | "*", .float =>
        -- (an int times a float, either way round: `2 * Id(1.5)`)
        if ctx.retries ≥ 3 then elabE ctx b (some ra.ty)
        else
          let c2 := { ctx with retries := ctx.retries + 1 }
          tryCatch (elabE c2 b (some ra.ty)) fun _ => elabE c2 b none
      | _, _ => elabE ctx b (some ra.ty)
    let rb := widenR ctx.types rb
    match op, ra.ty, rb.ty with
    | "+", .int, .int => return ⟨p2 .add ra.e rb.e, .int⟩
    | "-", .int, .int => return ⟨p2 .sub ra.e rb.e, .int⟩
    | "*", .int, .int => return ⟨p2 .mul ra.e rb.e, .int⟩
    -- floats (#127): no implicit int to float, except in `*` (`Count * 1.0`)
    | "+", .float, .float => return ⟨p2 .fadd ra.e rb.e, .float⟩
    | "-", .float, .float => return ⟨p2 .fsub ra.e rb.e, .float⟩
    | "*", .float, .float => return ⟨p2 .fmul ra.e rb.e, .float⟩
    | "*", .int, .float => return ⟨p2 .fmul (.prim .fofInt [ra.e]) rb.e, .float⟩
    | "*", .float, .int => return ⟨p2 .fmul ra.e (.prim .fofInt [rb.e]), .float⟩
    | "+", .arr t, .arr u =>
      if t == u then return ⟨p2 .concat ra.e rb.e, .arr t⟩
      -- arrays of classes concatenate at a common supertype (#32)
      match joinTy (← get).env (.arr t) (.arr u) exp with
      | some jt => return ⟨p2 .concat (← coerce p ra jt) (← coerce p rb jt), jt⟩
      | none => eerr p s!"cannot concatenate {ra.ty.show} and {rb.ty.show}"
    | _, ta, tb => eerr p s!"no operator '{op}' for {ta.show} and {tb.show}"
  | .cmp p a rest => elabCmp ctx p a rest
  | .andE _ a b =>
    -- each operand is its own scope: names defined in `a` are not visible in
    -- `b`, and names from either side do not escape the `and`
    let (ra, _) ← elabStmt ctx a none
    let (rb, _) ← elabStmt ctx b exp
    return ⟨Expr.andE ra.e rb.e, rb.ty⟩
  | .orE p a b =>
    let a := (Choice.takeFirst? a (choiceOrder ctx)).getD a
    let ra ← elabE { ctx with canFail := true, inTaking := true } a exp
    let rb ← match exp with
      | some _ => elabE ctx b exp
      | none =>
        if ctx.retries ≥ 3 then elabE ctx b (some ra.ty)
        else
          let c2 := { ctx with retries := ctx.retries + 1 }
          tryCatch (elabE c2 b (some ra.ty)) fun _ => elabE c2 b none
    let ty ← join p ra.ty rb.ty exp
    let t ← fresh ty
    return ⟨Expr.orE t (← coerce p ra ty) (← coerce p rb ty), ty⟩
  | .range p _ _ => eerr p "a range a..b can only be the source of a for clause"
  | .tuple _ [] => return ⟨.lit .void, .void⟩
  | .tuple _ es =>
    let exps : List (Option Ty) := match exp with
      | some (.tup ts) => if ts.length == es.length then ts.map some else es.map fun _ => none
      -- (a tuple where an array is expected becomes one: its elements at
      -- the element type)
      | some (.arr t) => es.map fun _ => some t
      | _ => es.map fun _ => none
    let rs ← (es.zip exps).mapM fun (e, t) => elabE ctx e t
    -- (an element that never gives a value, `return e`, `break`, `Err()`,
    -- has no type of its own in Verse Core, where a tuple whose type is
    -- inferred, as `not`'s operand is, needs one: without an expected type,
    -- it is followed by `void`, the type `never` stands for there, #285;
    -- with one, it is checked against it, as it has every type)
    let elems := (rs.zip exps).map fun (r, t) => match r.ty, t with
      | .never, none => Expr.seq r.e (.lit .void)
      | _, _ => r.e
    return ⟨.prim .mkTup elems, .tup (rs.map (·.ty))⟩
  | .block _ ss =>
    let (r, _) ← elabSeq ctx ss exp
    return r
  | .arrayLit p es =>
    let elemExp : Option Ty := match exp with
      | some (.arr t) => some t
      | _ => none
    match es with
    | [] => match elemExp with
      | some t => return ⟨.lit Value.emptyArray, .arr t⟩
      | none => eerr p "the type of an empty array{} must be given (e.g. X:[]int = array{})"
    | e :: rest =>
      let r ← elabE ctx e elemExp
      let t := elemExp.getD r.ty
      let rs ← rest.mapM fun e' => elabE ctx e' (some t)
      let all := (e :: rest).zip (r :: rs)
      -- the expected element type (or the first's), when every element
      -- converts to it; else the join of their types (classes at a common
      -- supertype, #67), with no element elaborated again
      match ← tryCatch (some <$> all.mapM fun (e', x) => coerce e'.pos x t) (fun _ => pure none) with
      -- (elements that never give a value, without an expected type: each
      -- followed by `void`, the type `never` stands for, as a tuple's, #285)
      | some es => return ⟨.prim .mkArr (if t == .never && elemExp.isNone then es.map (.seq · (.lit .void)) else es), .arr t⟩
      | none =>
        let jt ← (rest.zip rs).foldlM (fun acc ((e', x) : SExpr × R) => do
            match joinTy (← get).env acc x.ty elemExp with
            | some j => pure j
            | none =>
              if (elemExp.isNone || elemExp == some .any) && !ambiguousJoin (← get).env acc x.ty then
                pure .any
              else eerr e'.pos s!"the elements of this array have different types: {acc.show} and {x.ty.show}") r.ty
        let es ← all.mapM fun (e', x) => coerce e'.pos x jt
        -- (an element that never gives a value, joined with others, without
        -- an expected type: into a temporary of the joined type, so that the
        -- array's type can be inferred, #297)
        let es ← if elemExp.isSome then pure es else (es.zip all).mapM fun (e, (_, x)) => do
          if x.ty != .never then return e
          let t ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push jt })
          return Expr.assign t e
        return ⟨.prim .mkArr es, .arr jt⟩
  | .optionLit _ e =>
    let e := (Choice.takeFirst? e (choiceOrder ctx)).getD e
    let inner : Option Ty := match exp with
      | some (.opt t) => some t
      | _ => none
    let r ← elabE { ctx with canFail := true, inTaking := true } e inner
    -- an expression that cannot fail needs no failure context (and no
    -- saved state to roll back to: the interpreter's heap is not copied)
    -- (one that never gives a value, without an expected type: followed by
    -- `void`, the type `never` stands for in Verse Core, as in a tuple, #290)
    if !(r.e.mayFail ctx.sigProg) then
      let e := if r.ty == .never && inner.isNone then Expr.seq r.e (.lit .void) else r.e
      return ⟨.prim .mkSome [e], .opt r.ty⟩
    let t ← fresh r.ty
    return ⟨Expr.optionE t r.e, .opt r.ty⟩
  | .logicLit p e =>
    let e := (Choice.takeFirst? e (choiceOrder ctx)).getD e
    let r ← elabE { ctx with canFail := true, inTaking := true } e none
    if !(r.e.mayFail ctx.sigProg) && (← get).fnNeeds.isEmpty && (← get).methodNeeds.isEmpty && !ctx.typeOnly then eerr p "logic{…} needs an expression that can fail"
    return ⟨Expr.logicE r.e, .logic⟩
  | e@(.ite _ [.decl _ _ none false (.app _ (.ident _ "$methodCast") _ false)] _ (some _)) =>
    elabE ctx (pruneMethodCases ctx e) exp
  | e@(.ite _ [.decl _ _ none false (.app _ (.ident _ "$methodCase") _ false)] _ (some _)) =>
    elabE ctx (pruneMethodCases ctx e) exp
  | .ite p conds thenE elseE =>
    -- (#243, #351) a cast as a later clause of the condition, `if (c₁, …,
    -- D := T[X], rest) then B else E`, that only the first clause may be
    -- (one that refines type arguments, opens them, or goes through a
    -- view): as written first, and when that is refused for it, as `if (c₁,
    -- …) then (if (D := T[X], rest) then B else E) else E`, when the clauses
    -- before it have nothing its failure would undo (they print nothing,
    -- change no object, and call nothing, which might)
    -- (a clause `D := T[X]` past the first, which may be an index, `A[i]`,
    -- as written: the one the refusal is at)
    let castAt : List (Nat × Pos) := conds.zipIdx.filterMap fun
      | (.decl _ _ none false (.app q (.ident _ _) [_] true), i) => if i > 0 then some (i, q) else none
      | _ => none
    -- (as written for this `if` only: not the `if`s in it, nor those the
    -- cast's own path makes, #400's review)
    let asWritten := ctx.asWritten
    let ctx := { ctx with asWritten := false }
    if !asWritten && !castAt.isEmpty then
          let st0 ← get
          let tried ← tryCatch (do pure (Except.ok (← elabE { ctx with asWritten := true } (.ite p conds thenE elseE) exp)))
            fun err => pure (Except.error err)
          match tried with
          | .ok r => return r
          | .error err =>
            let some (k, _) := castAt.find? (fun (_, q) => err.startsWith s!"{q.show}:") | throw err
            if (err.splitOn "only as the first clause of an if's condition").length < 2 then throw err
            let castC := conds[k]!
            set st0
            -- (the clauses before it, apart: what they would leave behind)
            let pre := conds.take k
            let fx0 := (← get).fx
            let n0 := (← get).nslots
            modify fun s => { s with fx := [] }
            let (rp, _) ← tryCatch (elabSeq { ctx with canFail := true, inTaking := true, asWritten := true } pre none)
              fun _ => do set st0; throw err
            let fxP := (← get).fx
            set st0
            modify fun s => { s with fx := fx0 }
            -- (and a `var` set there, a slot they do not bind, which the
            -- failure would restore, #400's review)
            if rp.e.printsOrCalls || fxP.any (·.1 == "writes") || rp.e.assignsBelow n0 then
              throw s!"{err} (and the clauses before it print, change an object or a var, or call a function, which its failure would have to undo: put it first)"
            -- (the cast's branch is the elaborator's, not the source's: so a
            -- clause after it, always, `true?`, which the lift then carries,
            -- `made`)
            -- (`true?`, which may fail, keeps them a condition when they
            -- cannot fail themselves, as the whole condition could, as
            -- `Refine.castRest` does)
            let tq := SExpr.query p (.ident p "true")
            let innerC := castC :: conds.drop (k + 1) ++ [tq]
            match elseE with
            | none => return ← elabE ctx (.ite p (pre ++ [tq]) (.ite p innerC thenE none) none) exp
            | some ee =>
              -- (the `else` once, outside the clauses' names, #400's review:
              -- the branch gives an option of its value, or `true` for a
              -- `void` `if`, `false` when a clause fails, as #286's)
              let attempt (τ : Ty) : EM R := do
                let isVoid := τ == .void
                let v := s!"$lc{p.line}_{p.col}"
                let thenV : SExpr := if isVoid then .block p [thenE, .ident p "true"]
                  else .block p [.decl p v none false thenE, .optionLit p (.ident p v)]
                let outer := SExpr.ite p (pre ++ [tq]) (.ite p innerC thenV (some (.ident p "false")))
                  (some (.ident p "false"))
                let rty : Ty := if isVoid then .logic else .opt τ
                let r ← elabE ctx outer (some rty)
                let t ← fresh rty
                if isVoid then
                  let eE ← elabE ctx ee none
                  return ⟨.seq (.assign t r.e) (.ite (.prim .query [.local t]) (.lit .void) (.seq eE.e (.lit .void))), .void⟩
                let eE ← coerce p (← elabE ctx ee (some τ)) τ
                let xv ← fresh τ
                return ⟨.seq (.assign t r.e) (.ite (.assign xv (.prim .query [.local t])) (.local xv) eE), τ⟩
              match exp with
              | some τ => return ← attempt τ
              | none =>
                let st1 ← get
                let re ← elabE ctx ee none
                set st1
                if re.ty == .void then return ← attempt .void
                return ← tryCatch (attempt re.ty) fun _ => do set st1; attempt .void
    -- (a cast that refines type arguments, as the whole condition, #243,
    -- or as its first clause, the cast having no effects to undo when the
    -- rest fails: `if (D := T[X], rest) then B` is `if (D := T[X]) then (if
    -- (rest) then B)`, and with an `else E`, the branch's function gives
    -- `option{B}`, or `false` when the rest fails, and `E` runs once, in the
    -- caller, not under the refinement, #286)
    if let .decl dp d none false (.app _ (.ident _ T) [x] true) :: more := conds then
      match more, elseE with
      | [], _ =>
        match ← elabRefinedIf ctx p dp d T x thenE elseE exp with
        | some r => return r
        | none => pure ()
      | _, none =>
        match ← elabRefinedIf ctx p dp d T x (Refine.castRest p more thenE none) none exp (made := true) with
        | some r => return r
        | none => pure ()
      | _, some ee =>
        -- (at the if's type `τ`: void, the branch's function says whether
        -- the rest succeeded)
        -- (the branch runs outside any failure context, in the branch's
        -- function and in the caller, which keeps its result first: when
        -- it fails, the if fails, as a branch does; only `false`, the rest
        -- having failed, runs `E`)
        let attempt (τ : Ty) : EM (Option R) := do
          let isVoid := τ == .void
          let v := s!"$cv{p.line}_{p.col}"
          let thenV : SExpr := if isVoid then .block p [thenE, .ident p "true"]
            else .block p [.decl p v none false thenE, .optionLit p (.ident p v)]
          let inner := Refine.castRest p more thenV (some (.ident p "false"))
          let rty : Ty := if isVoid then .logic else .opt τ
          match ← elabRefinedIf ctx p dp d T x inner (some (.ident p "false")) (some rty) (made := true) with
          | some r =>
            let t ← fresh rty
            if isVoid then
              let eE ← elabE ctx ee none
              return some ⟨.seq (.assign t r.e) (.ite (.prim .query [.local t]) (.lit .void) (.seq eE.e (.lit .void))), .void⟩
            let eE ← coerce p (← elabE ctx ee (some τ)) τ
            let xv ← fresh τ
            return some ⟨.seq (.assign t r.e) (.ite (.assign xv (.prim .query [.local t])) (.local xv) eE), τ⟩
          | none => return none
        -- (without an expected type: the else's, else void, as a statement
        -- whose branches' types differ)
        -- (a later elaboration decides as the first did: by the result
        -- type of the function it asked for, `logic` for void)
        let r? ← match exp with
          | some t => attempt t
          | none => do
            let st0 ← get
            let re ← elabE ctx ee none
            set st0
            match ctx.types.castRequests.find? (·.key == Refine.keyOf p d (refineTagOf ctx)) with
            | some l => attempt (match l.ret with | .name "logic" => .void | _ => re.ty)
            | none =>
              if re.ty == .void then attempt .void
              else tryCatch (attempt re.ty) fun _ => attempt .void
        if let some r := r? then return r
    let (rc, ctxT) ← if Choice.hasChoice conds (choiceOrder ctx) then elabOneClauses { ctx with canFail := true } conds
      else elabSeq { ctx with canFail := true, inTaking := true } conds none
    -- (not while a function value is asked for, #214, #231: a call through
    -- it may fail once its class is made, in the elaboration that follows)
    if !(rc.e.mayFail ctx.sigProg) && (← get).fnNeeds.isEmpty && (← get).methodNeeds.isEmpty && !ctx.typeOnly then
      eerr p "the condition of this if cannot fail (Verse requires a failable condition)"
    let thenCtx := { ctxT with canFail := ctx.canFail, inTaking := ctx.inTaking }
    match elseE with
    | none =>
      let rt ← elabE thenCtx thenE (some .void)
      return ⟨.ite rc.e (← coerce p rt .void) (.lit .void), .void⟩
    | some ee =>
      -- (#366) a then branch that needs the else branch's type (`array{}`
      -- first): the else on its own first, then the then against it; when
      -- that fails too, the then branch's own error, as before
      let st0 ← get
      let rt? ← tryCatch (do pure (Except.ok (← elabE thenCtx thenE exp))) fun e => pure (Except.error e)
      let rt ← match rt? with
        | .ok rt => pure rt
        | .error err =>
          if exp.isSome || ctx.retries ≥ 3 then throw err
          let c2 := { ctx with retries := ctx.retries + 1 }
          let alt? ← tryCatch (do
              let re ← elabE c2 ee none
              let rt ← elabE { thenCtx with retries := ctx.retries + 1 } thenE (some re.ty)
              let ty ← join p rt.ty re.ty none
              pure (some ⟨Expr.ite rc.e (← coerce p rt ty) (← coerce p re ty), ty⟩)) fun _ => pure none
          match alt? with
          | some r => return r
          | none => throw err
      -- the else branch against the then branch's type (for `array{}`,
      -- `false`), else on its own, to join with it (#32)
      let re ← match exp with
        | some _ => elabE ctx ee exp
        | none =>
          if ctx.retries ≥ 3 then elabE ctx ee (some rt.ty)
          else
            let c2 := { ctx with retries := ctx.retries + 1 }
            tryCatch (elabE c2 ee (some rt.ty)) fun _ => elabE c2 ee none
      let ty ← join p rt.ty re.ty exp
      -- (#366) with nothing in common, the then branch against the else
      -- branch's type instead: `if (C) then false else option{4}` is a
      -- `?int`, as the other order is; else `any`, as before
      -- (from the state before the branches, the else on its own first:
      -- the first try's code and slots are not kept. Each retry raises
      -- `retries`, so an `if` nested n deep without a type is elaborated at
      -- most a constant number of times per level for the first three
      -- levels and once below: bounded, though multiplicative, tim-cc's
      -- review of #368)
      if ty == .any && exp.isNone && rt.ty != .any && re.ty != .any && ctx.retries < 3 then
        let stAfter ← get
        set st0
        let c2 := { ctx with retries := ctx.retries + 1 }
        match ← tryCatch (do
            let re' ← elabE c2 ee none
            let rt' ← elabE { thenCtx with retries := ctx.retries + 1 } thenE (some re'.ty)
            pure (some (rt', re'))) (fun _ => pure none) with
        | some (rt', re') =>
          if let some ty' := joinTy (← get).env rt'.ty re'.ty none then
            if ty' != .any then
              return ⟨.ite rc.e (← coerce p rt' ty') (← coerce p re' ty'), ty'⟩
          set stAfter
        | none => set stAfter
      return ⟨.ite rc.e (← coerce p rt ty) (← coerce p re ty), ty⟩
  | .forE p clauses body => do
    let returns := (Refine.findPart (fun | .ret .. => true | _ => false) false (.block p (clauses ++ [body]))).isSome
    let breaks := (ctx.inLoop || ctx.refineExits.brk.isSome) &&
      (Refine.findPart Refine.isBreak true (.block p clauses)).isSome
    let ownBreak ← if ctx.inLoop && breaks && ctx.forBreakSlot.isNone then
        some <$> fresh .logic
      else pure none
    let ctx := { ctx with
      forOutcomeSlot := none,
      forBreakSlot := ownBreak.orElse fun _ => if ctx.inLoop then ctx.forBreakSlot else none }
    let withExits : EM (R × Bool) := do
      let sourceRet ← match ctx.refineExits.ret with
        | some (some (_, t), _) => resolveTy ctx.types p t
        | some (none, _) => pure .void
        | none => match ctx.forReturnSlot.bind ctx.lookup with
          | some { ty := .opt t, .. } => pure t
          | _ => pure ctx.retTy
      let name := s!"$forReturn{p.line}_{p.col}_{ctx.locals.length}"
      let slot ← fresh (.opt sourceRet)
      let breakName := name ++ "$break"
      let breaking ← if breaks then some <$> fresh .logic else pure none
      let storage (n : String) : Option SourceStorage := if ctx.suspends then
        some { frame := ctx.frameName, name := n, args := ctx.frameArgs } else none
      let returnLocal : Local := { name, slot, ty := .opt sourceRet, mutable := true, storage := storage name }
      let breakLocal := breaking.map fun slot =>
        ({ name := breakName, slot, ty := .logic, mutable := true, storage := storage breakName } : Local)
      let extra := returnLocal :: breakLocal.toList
      modify fun st => { st with frameSlots := st.frameSlots ++ extra.filterMap (fun l => l.storage.map (l.slot, ·)) }
      let c := { ctx with locals := extra ++ ctx.locals }
      let flag ← fresh .logic
      let metadata := SExpr.set p (.ident p name) none (.ident p name)
      let metadata := if breaking.isSome then .block p [metadata, .set p (.ident p breakName) none (.ident p breakName)] else metadata
      let body := SExpr.app p (.ident p "$forReturns")
        [metadata, .ident p (if ctx.canFail then "true" else "false"), body] false
      let before ← get
      let r ← elabFor { c with forOutcomeSlot := some flag } p clauses body
      -- Only the consumer moves into a filter-bound continuation. Source
      -- cleanup and the final return remain in the suspending caller.
      let afterConsumer ← get
      let waits := forContWaits ctx before afterConsumer [r.e] && before.forStageUses == afterConsumer.forStageUses
      let result ← fresh (.opt r.ty)
      let value ← fresh r.ty
      let returning := s!"{name}$value"
      -- Break-only consumers can occur in a defer, branch or constructor,
      -- whose lexical checks must never see an invented source return.
      let ret ← if returns then
          elabE c (.ite p [.decl p returning none false (.query p (.ident p name))]
            (.ret p (some (.ident p returning))) none) (some .void)
        else pure ⟨.lit .void, .void⟩
      let failed := if ctx.canFail then Expr.prim .fail [] else .prim .userErr []
      let normal := Expr.ite (.assign value (.prim .query [.local result])) (.local value) failed
      let leaving := Expr.seq ret.e normal
      let leaving ← if breaking.isSome then do
          let stop ← elabE c (.ite p [.query p (.ident p breakName)] (Refine.liftedBreak p) none) (some .void)
          pure (Expr.seq stop.e leaving)
        else pure leaving
      let (run, after) ← if ctx.inLoop then do
          let escaped ← fresh .logic
          pure (Expr.seq (.assign escaped (.lit (.logic false))) (forwardForBreaks flag escaped r.e),
            Expr.ite (.prim .query [.local escaped]) .brk (.lit .void))
        else pure (r.e, Expr.lit .void)
      let code := Expr.seq (.assign slot (.lit .none))
        (.seq (.assign flag (.lit (.logic true)))
          (.seq (.assign result (.lit .none))
            (.seq (.loop (.seq (.assign result (.prim .mkSome [run])) Expr.brkV))
              (.seq after leaving))))
      let code := (breaking.map fun slot => Expr.seq (.assign slot (.lit (.logic false))) code).getD code
      return (⟨code, r.ty⟩, waits)
    let elaborate : EM R := do
      if !breaks && !returns then
        return ← elabFor ctx p clauses body
      if !ctx.suspends then return (← withExits).1
      -- Immediate consumers and staged waiting consumers carry source exits.
      -- Other waiting consumers retain their original source-return lowering.
      let st0 ← get
      if let some (r, waits) ← tryCatch (some <$> withExits) (fun _ => pure none) then
        if !waits then return r
      set st0
      elabFor ctx p clauses body
    let r ← elaborate
    return ⟨ownBreak.map (fun flag => Expr.seq (.assign flag (.lit (.logic false))) r.e) |>.getD r.e, r.ty⟩
  | .gen p _ _ _ => eerr p "a generator X : source can only appear in a for clause"
  | .loop _ body =>
    let lctx := { ctx with
      inLoop := true, inRepeat := true, loopDefers := ctx.defers.length,
      inChoice := false, forBreakSlot := none, forBreakCapture := none,
      refineExits := { ctx.refineExits with brk := none } }
    let r ← elabE lctx body none
    return ⟨.loop r.e, .void⟩
  | .brk p =>
    if ctx.inChoice then
      eerr p "break cannot leave the clauses of a failure context that has a choice (an if condition, first{…}, option{…}, …) (#208)"
    if !ctx.inLoop then
      eerr p (if ctx.inDefer then "break is only allowed inside loop (not for), and cannot leave a defer: block"
              else "break is only allowed inside loop (not for)")
    if let some name := ctx.forBreakCapture then
      let some target := ctx.lookup name | eerr p "internal: missing for break slot"
      if target.ty != .logic then eerr p "internal: invalid for break type"
      let ds ← elabDefers ctx ctx.defers
      let some pack := ctx.forExitPacket | eerr p "internal: missing for break outcome"
      let out ← elabE { ctx with defers := [] } pack (some ctx.retTy)
      return ⟨.seq ds (.seq (.assign target.slot (.lit (.logic true))) (.ret out.e)), .never⟩
    -- the defers of the scopes it leaves, inside its loop
    let ds ← elabDefers ctx (ctx.defers.take (ctx.defers.length - ctx.loopDefers))
    let jump := ctx.forBreakSlot.map (fun flag => Expr.seq (.assign flag (.lit (.logic true))) .brk) |>.getD .brk
    return ⟨.seq ds jump, .never⟩
  | .ret p e? =>
    if ctx.inParamDefault then eerr p "return is not allowed in a parameter's default"
    if ctx.inDefer then eerr p "return is not allowed in a defer: block"
    if ctx.inCtor then eerr p "return is not allowed in a constructor (it would skip the items after it)"
    if ctx.inBlock then eerr p "return is not allowed in a block: clause (it would skip the clauses after it)"
    if ctx.inBranch then eerr p "return is not allowed in a branch (Book of Verse ch. 14)"
    if let some (binding, pack) := ctx.refineExits.ret then
      let pre ← match binding, e? with
        | some (n, t), some e => pure [SExpr.decl p n (some t) false e]
        | some (_, t), none => eerr p s!"return needs a value of type {(← resolveTy ctx.types p t).show}"
        | none, some e => pure [e]
        | none, none => pure []
      return ← elabRefineExit ctx p pre pack
    -- Refining lifts above forward their return first. Here we are back
    -- in the owning continuation: save the operand before local cleanup,
    -- then return its abort packet with the latest mutable copy-outs.
    if let some name := ctx.forReturnSlot then
      let some target := ctx.lookup name | eerr p "internal: missing for return slot"
      let .opt ty := target.ty | eerr p "internal: invalid for return type"
      let value ← match e? with
        | some e => coerce p (← elabE ctx e (some ty)) ty
        | none =>
          if ty != .void then eerr p s!"return needs a value of type {ty.show}"
          pure (.lit .void)
      let saved ← fresh ty
      let ds ← elabDefers ctx ctx.defers
      let some pack := ctx.forExitPacket | eerr p "internal: missing for return outcome"
      let out ← elabE { ctx with defers := [] } pack (some ctx.retTy)
      return ⟨.seq (.assign saved value) (.seq ds
        (.seq (.assign target.slot (.prim .mkSome [.local saved])) (.ret out.e))), .never⟩
    let some e := e?
      | do
        if ctx.retTy != .void then eerr p s!"return needs a value of type {ctx.retTy.show}"
        return ⟨.seq (← elabDefers ctx ctx.defers) (.ret (.lit .void)), .never⟩
    let r ← elabE ctx e (some ctx.retTy)
    let v ← coerce p r ctx.retTy
    if ctx.defers.isEmpty then return ⟨.ret v, .never⟩
    -- the value first, then the defers of every scope it leaves
    let t ← fresh ctx.retTy
    return ⟨.seq (.assign t v) (.seq (← elabDefers ctx ctx.defers) (.ret (.local t))), .never⟩
  | .caseE p scrut arms => elabCase ctx p scrut arms exp
  | .decl p _ _ _ _ =>
    let (r, _) ← elabStmt ctx se exp
    let _ := p
    return r
  | .set p lhs op rhs => elabSet ctx p lhs op rhs

/-- A statement: like `elabE`, but a declaration extends the scope. Also
    enforces the failure discipline. -/
partial def elabStmt (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM (R × Ctx) := do
  let (r, ctx') ← match se with
    | .decl p n sty isVar rhs => do
      let (rhs, copied, envInit) := match rhs with
        | .app _ (.ident _ "$refineCopyIn") [e@(.ident _ source)] false => (e, (ctx.lookup source).bind (·.storage), false)
        | .app _ (.ident _ "$forEnvInit") [e@(.ident _ _)] false => (e, none, true)
        | e => (e, none, false)
      if let .app dp (.ident _ "$defer") _ _ := rhs then eerr dp "defer: is a statement: it has no value"
      checkNewLocal ctx p n
      let ty? ← sty.mapM (resolveTy ctx.types p)
      let r ← elabE ctx rhs ty?
      let ty := ty?.getD r.ty
      if ty == .never then
        eerr p (if n.startsWith "$" then "cannot infer the type of this clause's value" else s!"cannot infer the type of '{n}'")
      let e ← coerce p r ty
      let slot ← fresh ty
      let storage := copied.orElse (fun _ => ctx.resumeStorage.lookup n) |>.orElse fun _ => if isVar && ctx.suspends then
        some { frame := ctx.frameName, name := s!"{p.file}:{p.line}:{p.col}:{n}", args := ctx.frameArgs } else none
      if let some s := storage then
        modify fun st => { st with frameSlots := st.frameSlots ++ [(slot, s)] }
      if envInit then
        if let .local result := e then
          modify fun st => { st with frameCopies := st.frameCopies ++ [{ target := slot, result }] }
      pure (⟨.assign slot e, ty⟩,
        { ctx with locals := { name := n, slot, ty, mutable := isVar, storage } :: ctx.locals })
    | .app _ (.ident _ "$inlineScope") [.str _ [.text name]] false =>
      pure (⟨.lit .void, .void⟩, { ctx with inlineScopes := name :: ctx.inlineScopes })
    | .app _ (.ident _ "$inlineScopeEnd") [] false =>
      pure (⟨.lit .void, .void⟩, { ctx with inlineScopes := ctx.inlineScopes.drop 1 })
    | .app p (.ident _ "$methodParams") [.ident _ receiver, .str _ [.text method], .block _ ownTypes, .block _ args] _ => do
      let aliases ← ownTypes.mapM fun
        | .decl _ _ (some (.name n)) _ _ => pure n
        | _ => eerr p "internal: a method's type parameter"
      if aliases.all fun n => (ctx.types.tvars.lookup n).isSome then
        pure (⟨.lit .void, .void⟩, ctx)
      else
        let some receiverLocal := ctx.lookup receiver | eerr p "internal: missing method receiver"
        let .struct c _ := receiverLocal.ty | eerr p "method receiver is not a class or interface"
        let some owner := ctx.methodDecl? c method | eerr p s!"{c} has no method {method}"
        let root := (ctx.rootsOf c method).headD owner
        let implementations := ((ctx.types.concreteBelow c).map (ctx.implFor? · root method)).eraseDups
        let [some fname] := implementations
          | eerr p s!"cannot infer the type parameters of {method} from the arguments of this call"
        let some member := ctx.sig? fname | eerr p "internal: missing method declaration"
        -- Interface defaults may have been copied onto a concrete class
        -- after method extraction. Their generated function belongs to the
        -- original interface, whose parameters its receiver still supplies.
        let cls := member.scope.getD (fname.splitOn ".").head!
        if !ctx.types.isSub c cls then
          eerr p s!"cannot infer the type parameters of {method} from the arguments of this call"
        -- The member's checking stub has erased defaults. The generated
        -- implementation function retains their bodies and lexical scope.
        let implementation := Choice.methodFnName cls method
        let some sig := ctx.sig? implementation | eerr p "internal: missing method implementation"
        let saved ← get
        let packet ← elabGenericCallWith elabE { ctx with typeOnly := true, callInstanceProbe := some implementation }
          p sig (.ident p receiver :: args) none
        restoreConstructProbe ctx saved
        let .tup types := packet.ty | eerr p "internal: a method argument type packet"
        let own := types.drop ((ctx.types.sparams.lookup cls).getD []).length
        pure (⟨.lit .void, .void⟩, { ctx with types := { ctx.types with tvars := ctx.types.tvars ++ aliases.zip own } })
    | .app p (.ident _ "$methodType") [.ident _ receiver, .str _ [.text method], .block _ ownTypes] false => do
      let some receiverLocal := ctx.lookup receiver | eerr p "internal: missing method receiver"
      let .struct c args := receiverLocal.ty | eerr p "method receiver is not a class or interface"
      let some owner := ctx.methodDecl? c method | eerr p s!"{c} has no method {method}"
      let some sg := ctx.sig? s!"{owner}.{method}" | eerr p "internal: missing method declaration"
      let names := ((ctx.types.sparams.lookup owner).getD []).map (·.1)
      let types ← ownTypes.mapM fun
        | .decl q _ (some t) _ _ => resolveTy ctx.types q t
        | _ => eerr p "internal: a method's type argument"
      let own := (sg.tparams.drop names.length).map (·.1)
      let result := sg.ret.subst (names.zip (ctx.types.upArgs c args owner) ++ own.zip types)
      pure (⟨.lit .void, .void⟩, { ctx with types := { ctx.types with tvars := (receiver, result) :: ctx.types.tvars } })
    | .app _ (.ident _ "$declNames") ns false => do
      -- (#283) the names a block whose choice is lifted binds (renamed for
      -- the place): not in scope where the block is, as for its own
      for n in ns do
        if let .ident q n := n then checkNewLocal ctx q n
      pure (⟨.lit .void, .void⟩, ctx)
    | .app p (.ident _ "$freeNames") (.ident _ f :: ns) false => do
      -- (#283) the names an inlined body uses from outside: not bound
      -- here, where they would mean something else
      for n in ns.filterMap (fun | .ident _ n => some n | _ => none) do
        let member := match ctx.selfClass with
          | some c => ctx.hasMethod c n || (ctx.types.fields c).any (·.1 == n)
          | none => false
        if (ctx.lookup n).isSome || member then
          eerr p (s!"{f} has several values and uses {n}, which is also the name of a " ++
            s!"{if member then "member of Self" else "local"} here: rename one, as {f}'s body is inlined here, " ++
            s!"where {n} would mean that (#235, #283)")
      pure (⟨.lit .void, .void⟩, ctx)
    | .app p (.ident _ "$params") (.block _ decls :: tps) false => do
      -- (#235) an inlined generic call's parameters, bound together: its
      -- type arguments inferred from the arguments as at a call (each
      -- checked against its parameter's type once the type parameters it
      -- mentions are bound, else inferring them; `false`, `array{}` and
      -- `map{}` last), then named for the written types after
      let fname := match tps with | .ident _ f :: _ => f | _ => ""
      let cons : List (String × String) := tps.drop 1 |>.filterMap fun
        | .tuple _ [.ident _ n, .ident _ c] => some (n, c)
        | _ => none
      let names := cons.map (·.1)
      -- (as messages show them: the type parameters' own names)
      let shown (t : Ty) : String :=
        (t.subst (names.map fun n => (n, Ty.param ((n.dropWhile (· != '_')).drop 1).toString false))).show
      let penv : TyEnv := { ctx.types with tvars := ctx.types.tvars ++ cons.map fun (n, c) => (n, Ty.param n (c == "comparable")) }
      let items ← decls.mapM fun
        | .decl q x (some sty) v a => do pure (q, x, v, a, ← resolveTy penv q sty)
        | d => eerr d.pos "internal: a $params clause (#235)"
      let contextual := (← items.mapM (fun (_, _, _, a, _) => argNeedsTypeWith elabE ctx a)).toArray
      let mut σ : List (String × Ty) := []
      let mut done : Array (Option (Expr × Ty)) := Array.replicate items.length none
      let mut deferred : Array Bool := contextual
      for pass in [0, 1] do
        for ((q, _, _, a, t0), i) in items.zipIdx do
          if (pass == 0) == deferred[i]! then continue
          let t := t0.subst σ
          if t.params.any names.contains then
            if contextual[i]! then eerr q s!"cannot infer the type parameters of {fname} from the arguments of this call"
            let r ← elabE ctx a none
            match t.matchArg ctx.types σ r.ty with
            | some σ' =>
              σ := σ'.filter fun (v, _) => names.contains v
              let t' := t.subst σ
              if t'.params.any names.contains then
                if pass == 0 then deferred := deferred.set! i true
                else eerr q s!"cannot infer the type parameters of {fname} from this argument"
              else done := done.set! i (some (← coerce q r t', t'))
            | none => eerr q s!"expected {shown t}, found {r.ty.show} (in a call of {fname})"
          else
            done := done.set! i (some (← coerce q (← elabE ctx a (some t)) t, t))
      -- (a comparable type parameter's type argument must be comparable,
      -- as at a call)
      for (n, c) in cons do
        if c == "comparable" then
          if let some t := σ.lookup n then
            if !(isComparable ctx.types t) then
              eerr p (notComparable ctx.types t s!"{fname}'s type argument for {((n.dropWhile (· != '_')).drop 1).toString}")
      let mut code : Expr := .lit .void
      let mut c := ctx
      for ((q, x, v, _, _), d) in items.zip done.toList do
        let some (e, t) := d | eerr q s!"cannot infer the type parameters of {fname} from the arguments of this call"
        checkNewLocal c q x
        let slot ← fresh t
        code := .seq code (.assign slot e)
        c := { c with locals := { name := x, slot, ty := t, mutable := v } :: c.locals }
      pure (⟨.seq code (.lit .void), .void⟩, { c with types := { c.types with tvars := c.types.tvars ++ σ } })
    | .app p (.ident _ "$defaults") (.block _ decls :: tps) false => do
      -- (#283) the defaults an inlined generic call omits, after its
      -- `$params`, as at a call: in order, each seeing the parameters
      -- before it, at its parameter's type, or, when that mentions a type
      -- parameter nothing else determined, giving it its type argument;
      -- then every type parameter must have one
      let fname := Choice.shownFnName (match tps with | .ident _ f :: _ => f | _ => "")
      let cons : List (String × String) := tps.drop 1 |>.filterMap fun
        | .tuple _ [.ident _ n, .ident _ c] => some (n, c)
        | _ => none
      let shownTp (n : String) : String := ((n.dropWhile (· != '_')).drop 1).toString
      let open_ := cons.filter fun (n, _) => (ctx.types.tvars.lookup n).isNone
      let names := open_.map (·.1)
      let penv : TyEnv := { ctx.types with tvars := ctx.types.tvars ++ open_.map fun (n, c) => (n, Ty.param n (c == "comparable")) }
      let shown (t : Ty) : String := (t.subst (names.map fun n => (n, Ty.param (shownTp n) false))).show
      let fromContext : SExpr → Bool
        | .app _ (.ident _ "$paramDefault") [_, _, _, .ident _ "false"] false
        | .app _ (.ident _ "$paramDefault") [_, _, _, .arrayLit _ []] false
        | .app _ (.ident _ "$paramDefault") [_, _, _, .mapLit _ []] false => true
        | _ => false
      let mut σ : List (String × Ty) := []
      let mut code : Expr := .lit .void
      let mut c := ctx
      for d in decls do
        let .decl q x (some sty) v a := d | eerr d.pos "internal: a $defaults clause (#283)"
        let t := (← resolveTy penv q sty).subst σ
        let mut e : Expr := .lit .void
        let mut t' := t
        if t.params.any names.contains then
          if fromContext a then
            eerr p s!"cannot infer type parameter {shownTp ((t.params.filter names.contains).headD "t")} of {fname} from the arguments of this call"
          let r ← elabE c a none
          match t.matchArg ctx.types σ r.ty with
          | some σ' =>
            σ := σ'.filter fun (n, _) => names.contains n
            t' := t.subst σ
            e ← coerce q r t'
          | none => eerr q s!"expected {shown t}, found {r.ty.show} (the default of a parameter of {fname})"
        else
          e ← coerce q (← elabE c a (some t)) t
        checkNewLocal c q x
        let slot ← fresh t'
        code := .seq code (.assign slot e)
        c := { c with locals := { name := x, slot, ty := t', mutable := v } :: c.locals }
      for (n, k) in open_ do
        match σ.lookup n with
        | none => eerr p s!"cannot infer type parameter {shownTp n} of {fname} from the arguments of this call"
        | some t =>
          if k == "comparable" && !(isComparable ctx.types t) then
            eerr p (notComparable ctx.types t s!"{fname}'s type argument for {shownTp n}")
      pure (⟨.seq code (.lit .void), .void⟩, { c with types := { c.types with tvars := c.types.tvars ++ σ } })
    | _ => do pure (← elabE ctx se exp, ctx)
  if !ctx.canFail && (r.e.mayFail ctx.sigProg) then
    eerr se.pos ("this expression can fail, but it is not in a failure context (an if " ++
      "condition, a for clause, option{…}, logic{…}, not, the left of or, or a <decides> function)")
  return (r, ctx')

/-- `defer:` bodies, run in order (innermost first): each cannot fail, return
    or break out of itself, and sees the locals in scope where it is
    registered (Verse has no shadowing, so those at an exit include them). -/
partial def elabDefers (ctx : Ctx) (ds : List (SExpr × List Local)) : EM Expr := do
  elabDefersCore ctx ds

/-- Save the source return operand, unwind the lifted branch, then pack
    the exit flags and updated locals for its caller. -/
partial def elabRefineExit (ctx : Ctx) (p : Pos) (pre pack : List SExpr) : EM R := do
  if ctx.defers.isEmpty then
    let r ← elabE ctx (.block p (pre ++ pack)) (some ctx.retTy)
    return ⟨.ret (← coerce p r ctx.retTy), .never⟩
  let (r, c) ← elabSeq ctx pre none
  let ds ← elabDefers ctx ctx.defers
  let out ← elabE { c with defers := [] } (.block p pack) (some ctx.retTy)
  let e := Expr.seq ds (.ret (← coerce p out ctx.retTy))
  return ⟨if pre.isEmpty then e else .seq r.e e, .never⟩

/-- A suspension point with the code of the `defer:` blocks active there, in
    a branch that never runs (`if (false) …`), for the lowering's
    cancellation (#156): the defers run when a cancelled task unwinds. -/
partial def withDeferMark (ctx : Ctx) (e : Expr) : EM Expr := do
  if ctx.defers.isEmpty then return e
  return .seq (.ite (.prim .fail []) (← elabDefersCore ctx ctx.defers) (.lit .void)) e

/-- `sync:` (`isSync`) or `race:` with arms `arms` (#156): each arm's value
    goes to a slot (`race`: one slot of the arms' join type, written by the
    winner), and the arms to the marker `$syncMark(array{…})` (or
    `$raceMark`), which the lowering (`Suspend.lean`) runs concurrently. -/
partial def elabConc (ctx : Ctx) (p : Pos) (isSync : Bool) (arms : List SExpr) (exp : Option Ty)
    (isRush : Bool := false) : EM R := do
  let kw := if isSync then "sync" else if isRush then "rush" else "race"
  if !ctx.suspends then eerr p s!"{kw} suspends: it can only be used in a <suspends> function (#156)"
  if ctx.inDefer then eerr p s!"{kw} suspends, and a defer cannot suspend (#156)"
  if ctx.canFail then eerr p s!"{kw} suspends, and a failure context (a condition, a filter, or a <decides> call's arguments) cannot (#156)"
  if isRush && ctx.inRepeat then
    eerr p "rush cannot be in a loop or for body (Book of Verse ch. 14): call a function that rushes"
  let some mark := ctx.sig? (if isSync then "$syncMark" else if isRush then "$rushMark" else "$raceMark")
    | eerr p s!"internal error: no {kw} helper"
  -- (an arm is a scope of its own: its defers are its own, and break and
  -- return cannot leave it)
  let armCtx := { ctx with defers := [], loopDefers := 0, inLoop := false, inArm := true }
  if isSync then
    let mut stmts : Array Expr := #[]
    let mut slots : Array Nat := #[]
    let mut tys : Array Ty := #[]
    let mut async := 0
    -- (an expected tuple type gives each arm its expected type)
    let armExp : List (Option Ty) := match exp with
      | some (.tup ts) => if ts.length == arms.length then ts.map some else arms.map fun _ => none
      | _ => arms.map fun _ => none
    for (a, ae) in arms.zip armExp do
      let sourceBefore := (← get).pendingSourceSuspends
      let r ← elabE armCtx a ae
      let r ← match ae with
        | some t => pure ⟨← coerce a.pos r t, t⟩
        | none => pure r
      -- (a spawn or a branch in an arm does not make it wait)
      if sourceBefore != (← get).pendingSourceSuspends || ctx.sourceWaits r.e then async := async + 1
      let ty := if r.ty == .never then Ty.void else r.ty
      let t ← fresh ty
      stmts := stmts.push (.seq (.assign t r.e) (.lit .void))
      slots := slots.push t
      tys := tys.push ty
    if async < 2 then
      eerr p "sync needs at least two arms that can suspend (Book of Verse ch. 14): write the others in sequence"
    let e := Expr.seq (.call mark.idx [.prim .mkArr stmts.toList]) (.prim .mkTup (slots.toList.map Expr.local))
    return ⟨← withDeferMark ctx e, .tup tys.toList⟩
  else
    if arms.length < 2 then eerr p s!"{kw} needs at least two arms"
    -- the arms' join, as an `if`'s branches (or the expected type)
    let mut rs : Array (Pos × R) := #[]
    for a in arms do
      rs := rs.push (a.pos, ← elabE armCtx a exp)
    if isRush then
      noteBackgroundCaptures ctx (rs.toList.flatMap fun (_, r) => Suspend.slotsOf r.e)
    -- (as an `if`'s branches: void when one is, `any` when nothing else is
    -- common)
    let mut ty : Ty := .never
    for (_, r) in rs.toList do
      ty ← join p ty r.ty exp
    let rty := match exp with
      | some t => t
      | none => ty
    let t ← fresh rty
    let mut stmts : Array Expr := #[]
    for (ap, r) in rs do
      stmts := stmts.push (.seq (.assign t (← coerce ap r rty)) (.lit .void))
    let e := Expr.seq (.call mark.idx [.prim .mkArr stmts.toList]) (.local t)
    return ⟨← withDeferMark ctx e, rty⟩

/-- `spawn{F(…)}` (#156): a new task running the call, which must be of a
    `<suspends>` function; its arguments are evaluated now. The value is
    the task, a `task(t)`. The lowering (`Suspend.lean`) turns the marker
    `$spawnMark(array{F(…), T})` into a new task root. -/
partial def elabSpawn (ctx : Ctx) (p : Pos) (body : SExpr) : EM R := do
  let sourceBefore := (← get).pendingSourceSuspends
  if ctx.inDefer then eerr p "spawn in a defer is not supported (#156)"
  if ctx.canFail && !ctx.inDefaultCheck then
    eerr p "spawn cannot be in a failure context (a condition, a filter, or a <decides> call's arguments) (#156)"
  let some mark := ctx.sig? "$spawnMark"
    | eerr p "spawn{…} takes a call of a <suspends> function (#156)"
  let call := match body with
    | .block _ [e] => e
    | e => e
  if let .app q (.member mp obj m0) args br := call then
    let isSuper := match obj with | .ident _ "(super:)" => true | _ => false
    if !isSuper then
      let saved ← get
      let rx ← elabE { ctx with defers := [], suspends := true, canFail := false } obj none
      if let .struct c _ := rx.ty then
        let (owner, m) := if m0.startsWith "(" then
          match (m0.drop 1).toString.splitOn ":)" with
          | [owner, m] => (owner, m)
          | _ => (c, m0)
          else (c, m0)
        let method := (ctx.methodDecl? owner m).isSome ||
          ((ctx.types.methodOverloads.lookup m).getD []).any fun o => (ctx.methodDecl? owner o).isSome
        if ctx.types.classes.contains c && method then
          let isS (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.suspends
          if Suspend.countSusp isS (fun _ => false) false (· == mark.idx) rx.e > 0 then
            eerr p "the arguments of a spawned call cannot suspend (#156)"
          let slot ← fresh rx.ty
          let name := s!"$spawnReceiver{slot}"
          let cctx := { ctx with locals := { name, slot, ty := rx.ty, mutable := false } :: ctx.locals }
          let r ← elabApp { cctx with defers := [], suspends := true, canFail := false } q
            (.member mp (.ident mp name) ("$spawnMethod:" ++ m0)) args br none
          modify fun st => { st with pendingSourceSuspends := sourceBefore }
          return ⟨.seq (.assign slot rx.e) r.e, r.ty⟩
      set saved
  -- Function values use their interface's spawn dispatch, including fields
  -- and returned values. That path remains typed when a requested adapter
  -- has not been generated yet. Save the value once before its arguments.
  if let .app q f args br := call then
    let value := match f with
      | .ident _ n => (ctx.lookup n).isSome || ctx.selfClass.any (fun c =>
          (ctx.types.fields c).any (·.1 == n))
      | _ => true
    if value then
      let saved ← get
      let rx? ← tryCatch (some <$> elabE { ctx with defers := [], suspends := true, canFail := false } f none)
        (fun _ => pure none)
      if let some rx := rx? then
        if let .struct shape _ := rx.ty then
          if (FnValues.parseName shape).isSome then
            let isS (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.suspends
            if Suspend.countSusp isS (fun _ => false) false (· == mark.idx) rx.e > 0 then
              eerr p "the arguments of a spawned call cannot suspend (#156)"
            let slot ← fresh rx.ty
            let name := s!"$spawnValue{slot}"
            let cctx := { ctx with locals := { name, slot, ty := rx.ty, mutable := false } :: ctx.locals }
            let r ← elabApp { cctx with defers := [], suspends := true, canFail := false } q
              (.member f.pos (.ident f.pos name) ("$spawnMethod:" ++ FnValues.callOf shape)) args br none
            return ⟨.seq (.assign slot rx.e) r.e, r.ty⟩
      set saved
  -- (the call runs in the new task, which may wait, also when spawned from
  -- an immediate function; its arguments may not)
  let r ← elabE { ctx with defers := [], suspends := true, canFail := false } call none
  let isS : Nat → Bool := fun f => ctx.sigs.any fun s => s.idx == f && s.suspends
  let e := match r.e with
    | .seq (.ite (.prim .fail []) _ (.lit .void)) e => e
    | e => e
  -- (statements before the call, such as a method call's receiver, run
  -- now, as the arguments are evaluated)
  -- (a method with several implementations: the dispatch on the
  -- receiver's class, a chain of tests that the lowering makes a function
  -- of the slots it uses, #173)
  let rec peel : Expr → Option (List Expr × Expr)
    | .call g es => some ([], .call g es)
    | .seq a b => (peel b).map fun (ps, c) => (a :: ps, c)
    | e@(.ite ..) => if Suspend.isDispatchChain e then some ([], e) else none
    -- (one refined by #142, through a temporary of the result type)
    | .assign _ e@(.ite ..) => if Suspend.isDispatchChain e then some ([], e) else none
    | _ => none
  let some (pre, callE) := peel e
    | eerr p "spawn{…} takes one call of a <suspends> function or method, with its arguments (#156)"
  let dispatch := match callE with | .assign _ e => e | e => e
  let arms := Suspend.chainArms dispatch
  let (ok, es) := match callE with
    | .call g es => (isS g, es)
    -- (each implementation the dispatch runs, with its own defaults)
    | _ => (!arms.isEmpty && arms.all (fun a => (Suspend.callsOf a).any (isS ·.1)), [])
  if !ok then eerr p "spawn{…} takes a call of a <suspends> function (#156)"
  -- (a spawn among them does not wait)
  let waits (x : Expr) := Suspend.countSusp isS (fun _ => false) false (· == mark.idx) x
  -- A dispatch arm includes the selected method call itself. Any other
  -- suspension belongs to its arguments, including inline defaults.
  if (pre ++ es).any (fun x => waits x > 0) || arms.any (fun x => waits x > 1) then
    eerr p "the arguments of a spawned call cannot suspend (#156)"
  let ty : Ty := .struct "task" [r.ty]
  let tagT := ctx.types.tagOf "task"
  let t ← fresh ty
  -- (its fields: the done flag `false`, the others empty options)
  let fieldVals := (ctx.types.fields "task" [r.ty]).map fun (_, ft, _) =>
    if ft == .logic then Expr.lit (.logic false) else Expr.lit .none
  let spawnE : Expr := .seq (.assign t (.heap (.new tagT) fieldVals))
    (.seq (.call mark.idx [.prim .mkArr [.seq callE (.lit .void), .seq (.local t) (.lit .void)]]) (.local t))
  modify fun st => { st with pendingSourceSuspends := sourceBefore }
  return ⟨pre.foldr Expr.seq spawnE, ty⟩

/-- `branch:` (#156): its body runs as a background task over the enclosing
    function's frame, at once up to its first wait, and is cancelled when
    the function exits. The lowering (`Suspend.lean`) turns the marker
    `$branchMark(array{body})` into an arm run as a task root. -/
partial def elabBranch (ctx : Ctx) (p : Pos) (body : SExpr) : EM R := do
  if !ctx.suspends then eerr p "branch suspends: it can only be used in a <suspends> function (#156)"
  if ctx.inDefer then eerr p "branch in a defer is not supported (#156)"
  if ctx.canFail then eerr p "branch cannot be in a failure context (a condition, a filter, or a <decides> call's arguments) (#156)"
  if ctx.inRepeat then eerr p "branch cannot be in a loop or for body (Book of Verse ch. 14): call a function that branches"
  let some mark := ctx.sig? "$branchMark" | eerr p "internal error: no branch helper"
  let armCtx := { ctx with defers := [], loopDefers := 0, inLoop := false, inArm := true, inBranch := true }
  let sourceBefore := (← get).pendingSourceSuspends
  let r ← elabE armCtx body none
  modify fun st => { st with pendingSourceSuspends := sourceBefore }
  noteBackgroundCaptures ctx (Suspend.slotsOf r.e)
  return ⟨.call mark.idx [.prim .mkArr [.seq r.e (.lit .void)]], .void⟩

partial def elabDefersCore (ctx : Ctx) (ds : List (SExpr × List Local)) : EM Expr := do
  let mut acc : Expr := .lit .void
  for (d, locs) in ds.reverse do
    -- (with the locals where it was registered: their slots still hold them)
    -- (no failure context that takes a choice's values, #283)
    let dctx := { ctx with canFail := false, inDefer := true, inLoop := false, defers := [], loopDefers := 0,
                           locals := locs, inTaking := false, liftWhy := "" }
    let r ← elabE dctx d none
    acc := .seq r.e acc
  return acc

/-- A call of an overloaded function or method (#74): the one overload
    (`ovs`, each with its signature `sigOf`, a method's without `Self`) the
    call's shape and arguments fit, then `call` it. -/
partial def resolveOverload (ctx : Ctx) (p : Pos) (name : String) (ovs : List String)
    (sigOf : String → Option Sig) (call : String → EM R) (args : List SExpr) : EM R := do
  -- an overloaded function (#74): the one overload whose parameters the
  -- arguments fit (each elaborated at the parameter's type, in a trial)
  -- the overloads the call's shape fits: as many positional arguments, and
  -- named ones the overload has, every one it needs given
  let isNamedArg : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
  let posArgs := args.filter (!isNamedArg ·)
  let namedArgs : List (String × SExpr) := args.filterMap fun
    | .decl _ n _ _ rhs => if n.startsWith "?" then some ((n.drop 1).toString, rhs) else none
    | _ => none
  let fitsShape (s : Sig) : Bool :=
    posArgs.length == s.params.length - s.named.length &&
    namedArgs.all (fun (g, _) => s.named.any (·.1 == g)) &&
    s.named.all fun (n, d) => d.isSome || namedArgs.any (·.1 == n)
  -- each argument expression with the type of its parameter in `s`
  let argTys (s : Sig) : List (SExpr × Ty) :=
    let npos := s.params.length - s.named.length
    (posArgs.zip (s.params.take npos)) ++ namedArgs.filterMap fun (n, rhs) =>
      (s.named.findIdx? (·.1 == n)).map fun j => (rhs, (s.params.drop npos).getD j .void)
  let cands := ovs.filter fun o => ((sigOf o).map fitsShape).getD false
  -- each argument's type alone, once (none: it needs an expected type)
  let natTy (a : SExpr) : EM (Option Ty) := do
    -- (by position and shallow shape: a wrong hit could only make the
    -- call below fail to elaborate, never take an overload the arguments
    -- do not fit, as no call fits two)
    let shape : String := match a with
      | .app _ (.ident _ f) as b => s!"app {f} {as.length} {b}"
      | .ident _ n => s!"id {n}"
      | .int _ v => s!"int {v}"
      | .member _ _ m => s!"mem {m}"
      | .construct _ n _ fs => s!"new {n} {fs.length}"
      | .tuple _ es => s!"tup {es.length}"
      | .arrayLit _ es => s!"arr {es.length}"
      | .bin _ o _ _ => s!"bin {o}"
      | _ => "_"
    let key := s!"{a.pos.line}:{a.pos.col}:{a.pos.file}:{shape}"
    if let some r := (← get).natTys[key]? then return r
    let st ← get
    let r ← tryCatch (do return some (← elabE ctx a none).ty) (fun _ => pure none)
    let cache := (← get).natTys
    set { st with natTys := cache.insert key r, methodReceivers := (← get).methodReceivers }
    return r
  let coercible (t u : Ty) : EM Bool := do
    let st ← get
    let ok ← tryCatch (do discard <| coerce p ⟨.lit .void, t⟩ u; pure true) (fun _ => pure false)
    set { st with natTys := (← get).natTys, methodReceivers := (← get).methodReceivers }
    return ok
  let mut byNat : List String := []
  for o in cands do
    let some so := sigOf o | continue
    let mut ok := true
    if cands.length > 1 then
      -- (a generic one's patterns, by the matching that infers its type
      -- arguments: no whole-call trial at every level of a nested call)
      let mut σ : List (String × Ty) := []
      for (a, u) in argTys so do
        if let some t ← natTy a then
          if so.tparams.isEmpty then
            if !(← coercible t u) then ok := false
          else match u.matchArg ctx.types σ t with
            | some σ' => σ := σ'
            | none =>
              -- (against nothing bound: the pattern cannot take it; a
              -- conflict with earlier bindings only may be a subtype the
              -- call reconciles, so the candidate stays for the trial)
              if (u.matchArg ctx.types [] t).isNone && !(← coercible t u) then ok := false
    if ok then byNat := byNat ++ [o]
  let fits (o : String) : EM Bool := do
    let s := (sigOf o).get!
    let st ← get
    if !s.tparams.isEmpty then
      let ok ← tryCatch (do discard <| call o; pure true) (fun _ => pure false)
      set { st with natTys := (← get).natTys, methodReceivers := (← get).methodReceivers }
      return ok
    let ok ← tryCatch (do
        for (a, t) in argTys s do
          let r ← elabE ctx a (some t)
          discard <| coerce a.pos r t
        pure true) (fun _ => pure false)
    set { st with natTys := (← get).natTys, methodReceivers := (← get).methodReceivers }
    return ok
  -- the overloads the arguments' own types fit, then those the arguments
  -- elaborated at each one's parameter types fit
  let mut ok : List String := []
  if byNat.length == 1 then ok := byNat
  else
    -- (none: an argument's own type can differ from its type at a
    -- parameter, `false` is a logic and also fits `?t`)
    for o in (if byNat.isEmpty then cands else byNat) do
      if ← fits o then ok := ok ++ [o]
  let call' (o : String) : EM R :=
    tryCatch (call o) fun msg => throw (msg.replace o name)
  match ok, cands with
  | [o], _ => call' o
  | [], [o] => call' o   -- its error
  | [], [] =>
    let nm := if namedArgs.isEmpty then "" else s!" and {", ".intercalate (namedArgs.map fun (n, _) => s!"?{n}")}"
    let shown := ovs.filterMap fun o => (sigOf o).map fun so =>
      let npos := so.params.length - so.named.length
      "(" ++ ", ".intercalate ((so.params.take npos).map Ty.show ++
        (so.named.zip (so.params.drop npos)).map fun ((n, d), t) =>
          s!"?{n}:{t.show}" ++ (if d.isSome then " = …" else "")) ++ ")"
    eerr p s!"no overload of {name} fits a call with {posArgs.length} positional argument(s){nm}; its overloads take {" and ".intercalate shown}"
  | [], _ =>
    let st ← get
    let tys ← posArgs.mapM fun a => do return (← elabE ctx a none).ty.show
    let ntys ← namedArgs.mapM fun (n, a) => do return s!"?{n}:{(← elabE ctx a none).ty.show}"
    let tys := tys ++ ntys
    set st
    eerr p s!"no overload of {name} takes ({", ".intercalate tys})"
  | _ :: _ :: _, _ =>
    let shown := ok.map fun o => s!"({", ".intercalate (((sigOf o).map (·.params)).getD [] |>.map Ty.show)})"
    eerr p s!"this call of {name} fits more than one overload: {" and ".intercalate shown}"

/-- A sequence of statements, threading the scope; the value is the last one's. -/
partial def elabSeq (ctx : Ctx) (ss : List SExpr) (exp : Option Ty) : EM (R × Ctx) := do
  match ss with
  | [] => return (⟨.lit .void, .void⟩, ctx)
  | .app p (.ident _ "$defer") [body] false :: rest =>
    -- `defer: D` then the rest of the scope (Book of Verse ch. 7): the rest,
    -- with D pending for its returns and breaks, then D, then the rest's value
    if let .block _ [] := body then eerr p "a defer: block cannot be empty"
    let (r2, ctx2) ← elabSeq { ctx with defers := (body, ctx.locals) :: ctx.defers } rest exp
    let d ← elabDefers ctx [(body, ctx.locals)]
    let ctx2 := { ctx2 with defers := ctx.defers, loopDefers := ctx.loopDefers }
    match r2.ty with
    | .never => return (r2, ctx2)
    | .void => return (⟨.seq r2.e (.seq d (.lit .void)), .void⟩, ctx2)
    | ty =>
      let t ← fresh ty
      return (⟨.seq (.assign t r2.e) (.seq d (.local t)), ty⟩, ctx2)
  | [s] => elabStmt ctx s exp
  | s :: rest =>
    let (r, ctx') ← elabStmt ctx s none
    let (r2, ctx'') ← elabSeq ctx' rest exp
    return (⟨.seq r.e r2.e, r2.ty⟩, ctx'')

partial def elabArgs (ctx : Ctx) (p : Pos) (args : List SExpr) (tys : List Ty) : EM (List Expr) := do
  if args.length != tys.length then
    eerr p s!"expected {tys.length} argument(s), found {args.length}"
  (args.zip tys).mapM fun (a, t) => do coerce a.pos (← elabE ctx a (some t)) t

partial def elabInts (ctx : Ctx) (p : Pos) (args : List SExpr) : EM (List Expr) :=
  elabArgs ctx p args (args.map fun _ => .int)

/-- A call. One tuple argument that a call cannot take as it is is expanded
    into several (Book of Verse ch. 3, #140): of a method, an overloaded or a
    generic function as of any other (`elabAppBase` does plain calls). -/
partial def elabApp (ctx : Ctx) (p : Pos) (f : SExpr) (args : List SExpr) (bracket : Bool)
    (exp : Option Ty) : EM R := do
  let isNamed : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
  let positional := args.filter (!isNamed ·)
  let namedArgs := args.filter isNamed
  -- A generated method function keeps its receiver as the first argument.
  -- Inlining already spreads a following tuple, but kept/scalar/array calls
  -- reach this boundary directly. Instantiate from the actual receiver;
  -- callee type names have no meaning in the caller's lexical type scope.
  if let (.ident _ g, [receiver, tupleArg]) := (f, positional) then
    if let some s := ctx.sig? g then
      let npos := s.params.length - s.named.length
      if s.pnames.head? == some "$Self" && npos ≥ 3 then
        let r ← elabE ctx receiver none
        let some σ := s.params[0]!.matchArg ctx.types [] r.ty
          | eerr receiver.pos s!"expected {s.params[0]!.show}, found {r.ty.show} (the receiver of {Choice.shownFnName g})"
        let pattern := Ty.tup (s.params.drop 1 |>.take (npos - 1))
        let known := pattern.params.all fun n => (σ.lookup n).isSome
        let rv ← fresh r.ty
        let rn := s!"$methodReceiver{rv}"
        let c := { ctx with locals := { name := rn, slot := rv, ty := r.ty, mutable := false } :: ctx.locals }
        if !known then
          if let .tuple _ fields := tupleArg then
            let out ← elabAppBase c p f (.ident p rn :: fields ++ namedArgs) bracket exp
            return ⟨.seq (.assign rv r.e) out.e, out.ty⟩
          let tuple ← elabE ctx tupleArg none
          let .tup ts := tuple.ty
            | eerr tupleArg.pos s!"expected tuple argument of {Choice.shownFnName g}, found {tuple.ty.show}"
          let tv ← fresh tuple.ty
          let tn := s!"$methodTuple{tv}"
          let c := { c with locals := { name := tn, slot := tv, ty := tuple.ty, mutable := false } :: c.locals }
          let parts := ts.zipIdx.map fun (_, i) =>
            SExpr.app tupleArg.pos (.ident tupleArg.pos tn) [.int tupleArg.pos (i : Int)] false
          let out ← elabAppBase c p f (.ident p rn :: parts ++ namedArgs) bracket exp
          return ⟨.seq (.assign rv r.e) (.seq (.assign tv tuple.e) out.e), out.ty⟩
        let ty := pattern.subst σ
        let tuple ← coerce tupleArg.pos (← elabE ctx tupleArg (some ty)) ty
        let tv ← fresh ty
        let tn := s!"$methodTuple{tv}"
        let c := { c with locals := { name := tn, slot := tv, ty, mutable := false } :: c.locals }
        let parts := (List.range (npos - 1)).map fun (i : Nat) =>
          SExpr.app tupleArg.pos (.ident tupleArg.pos tn) [.int tupleArg.pos (i : Int)] false
        let out ← elabAppBase c p f (.ident p rn :: parts ++ namedArgs) bracket exp
        return ⟨.seq (.assign rv r.e) (.seq (.assign tv tuple) out.e), out.ty⟩
  -- A literal tuple's fields are the call's positional arguments. Let the
  -- ordinary binder infer generic instances before contextual empty fields,
  -- including in the retained body used to check a multi-value function.
  if let (.ident _ g, [.tuple _ fields]) := (f, positional) then
    if let some s := ctx.sig? g then
      let selfMember := ctx.selfClass.any fun c => ctx.hasMethod c g ||
        ((ctx.types.methodOverloads.lookup g).map (·.any (ctx.hasMethod c ·))).getD false ||
        ((ctx.types.fields c).any (·.1 == g) && !builtins.contains g && !softBuiltins.contains g)
      if (ctx.lookup g).isNone && !selfMember && s.params.length - s.named.length > 1 then
        return ← elabAppBase ctx p f (fields ++ namedArgs) bracket exp
  match positional with
  | [a] =>
    -- (nested retries are bounded: each level elaborates its argument again)
    if ctx.retries ≥ 8 then return ← elabAppBase ctx p f args bracket exp
    let saved ← get
    -- (the state is restored between attempts, but not the overload cache)
    let restore : EM Unit := do set { saved with natTys := (← get).natTys, methodReceivers := (← get).methodReceivers }
    tryCatch (elabAppBase ctx p f args bracket exp) fun err => do
      -- (only a call refused for its arguments' shape is tried again: an
      -- error from inside the argument is the argument's)
      let shapeErr := ["argument(s)", "overload", "expected tuple"].any fun k => (err.splitOn k).length > 1
      if !shapeErr then throw err
      restore
      let c2 := { ctx with retries := ctx.retries + 1 }
      -- a method's receiver is evaluated first, then the tuple
      let (pre, c2, f') ← match f with
        | .member mp obj m =>
          if (match obj with | .ident _ "(super:)" => true | _ => false) then pure ([], c2, f) else
          match ← tryCatch (some <$> elabE c2 obj none) (fun _ => pure none) with
          | some ro =>
            let to ← fresh ro.ty
            let nm := s!"$receiver{to}"
            pure ([Expr.assign to ro.e],
              { c2 with locals := { name := nm, slot := to, ty := ro.ty, mutable := false } :: c2.locals },
              SExpr.member mp (.ident mp nm) m)
          | none => pure ([], c2, f)
        | _ => pure ([], c2, f)
      match ← tryCatch (some <$> elabE c2 a none) (fun _ => pure none) with
      | some ⟨e, .tup ts⟩ =>
        if ts.length < 2 then restore; throw err
        let tt ← fresh (.tup ts)
        let nm := s!"$tuple{tt}"
        let c3 := { c2 with locals := { name := nm, slot := tt, ty := .tup ts, mutable := false } :: c2.locals }
        let parts := (List.range ts.length).map fun (i : Nat) => SExpr.app a.pos (.ident a.pos nm) [.int a.pos (i : Int)] false
        match ← tryCatch (some <$> elabAppBase c3 p f' (parts ++ namedArgs) bracket exp) (fun _ => pure none) with
        | some r => return ⟨(pre ++ [Expr.assign tt e]).foldr Expr.seq r.e, r.ty⟩
        | none => restore; throw err
      | _ => restore; throw err
  | _ => elabAppBase ctx p f args bracket exp

partial def elabAppBase (ctx : Ctx) (p : Pos) (f : SExpr) (args : List SExpr) (bracket : Bool)
    (exp : Option Ty) : EM R := do
  let needBracket (name : String) : EM Unit := do
    if !bracket then eerr p s!"{name} can fail: call it with {name}[…]"
  match f with
  | .ident _ name =>
    match ctx.lookup name with
    | some l => elabIndexLike ctx p ⟨.local l.slot, l.ty⟩ args bracket
    | none =>
    -- in a method, a method of `Self`, or a field of `Self` indexed
    let selfMember? : Bool := match ctx.selfClass with
      | some c => ctx.hasMethod c name ||
          ((ctx.types.methodOverloads.lookup name).map (·.any (ctx.hasMethod c ·))).getD false ||
          ((ctx.types.fields c).any (·.1 == name) && !builtins.contains name && !softBuiltins.contains name)
      | none => false
    if selfMember? then elabApp ctx p (.member p (.ident p "Self") name) args bracket exp else
    -- `T[X]`, `T(X)`: a cast to class or interface `T`
    if ctx.types.classes.contains name && (ctx.sig? name).isNone then elabCast ctx p name args bracket else
    if let some (base, conds) := ctx.types.refines.lookup name then
      -- `age[X]` (#136): `X`, if it meets the conditions; failing otherwise
      if !bracket then eerr p s!"a cast to {name} can fail: write {name}[X]"
      let [a] := args | eerr p s!"a cast to {name} takes one value"
      let r ← elabE ctx a (some base)
      let r := widenR ctx.types r
      if r.ty != base then eerr p s!"a cast to {name} takes {withArticle base.show}, found {r.ty.show}"
      let tv ← fresh base
      let isF := base == .float
      let test (c : String × Value) : Expr :=
        let op : Prim := match c.1, isF with
          | "<", false => .lt | "<=", false => .le | ">", false => .gt | _, false => .ge
          | "<", true => .flt | "<=", true => .fle | ">", true => .fgt | _, true => .fge
        p2 op (.local tv) (.lit c.2)
      let checks := conds.foldr (fun c acc => Expr.seq (test c) acc) (.local tv)
      return ⟨.seq (.assign tv r.e) checks, .refine name⟩
    else
    if let some ovs := ctx.types.overloads.lookup name then
      resolveOverload ctx p name ovs ctx.sig? (fun o => do
        -- (#283) the overload an `$inlineOv`'s call as written takes
        if let some (id, f) := ctx.ovPick then
          if f == name then modify fun st => { st with ovPicks := (id, o) :: st.ovPicks }
        elabApp { ctx with ovPick := none } p (.ident p o) args bracket exp) args
    else
    -- (a soft built-in the program defines is the program's)
    let builtinName := if (softBuiltins.contains name || name == "any") && (ctx.sig? name).isSome then "$program" else name
    match builtinName with
    | "Concatenate" =>
      -- (#150) an array of arrays flattened, or several arrays one after
      -- the other (as a tuple of them converts to an array of arrays)
      match args with
      | [] => match exp with
        | some (.arr t) => return ⟨.lit Value.emptyArray, .arr t⟩
        | _ => eerr p "Concatenate() needs an expected array type"
      | [a] =>
        let r ← elabE ctx a (match exp with | some t => some (.arr t) | none => none)
        match r.ty with
        | .arr (.arr t) =>
          -- (through a typed temporary: an empty literal has no type of its own)
          let tv ← fresh r.ty
          return ⟨.seq (.assign tv r.e) (.prim .flatten [.local tv]), .arr t⟩
        | t => eerr p s!"Concatenate takes arrays, or an array of arrays, found {t.show}"
      | a :: rest =>
        let r0 ← elabE ctx a exp
        let .arr t := r0.ty | eerr a.pos s!"Concatenate takes arrays, found {r0.ty.show}"
        let mut acc := r0.e
        for b in rest do
          let rb ← elabE ctx b (some (.arr t))
          acc := p2 .concat acc (← coerce b.pos rb (.arr t))
        return ⟨acc, .arr t⟩
    | "any" =>
      -- `any(X)`: X as an `any` (#138), evaluated
      let [a] := args | eerr p "any(…) takes one value"
      let r ← elabE ctx a none
      return ⟨← coerce a.pos r .any, .any⟩
    | "Print" =>
      let es ← elabArgs ctx p args [Ty.string]
      return ⟨.print es.head!, .void⟩
    | "ConcatenateMaps" =>
      -- the entries of every map, a later map's value winning for a key (Book
      -- of Verse ch. 9): the first copied, then each other's pairs put in turn
      let some a0 := args.head? | eerr p "ConcatenateMaps takes at least one map"
      -- the maps' type: the expected one, else the first argument's that has
      -- one alone (an empty map{} has none)
      let mapExp : Option Ty ← match exp with
        | some t@(.map ..) => pure (some t)
        | _ =>
          let st ← get
          let mut found : Option Ty := none
          for a in args do
            if found.isNone then
              found ← tryCatch (do let r ← elabE ctx a none; pure (match r.ty with | t@(.map ..) => some t | _ => none))
                (fun _ => pure none)
          set st
          pure found
      let mut rs : Array R := #[]
      let mut jt? : Option Ty := none
      for a in args do
        let r ← elabE ctx a mapExp
        let .map _ _ := r.ty | eerr a.pos s!"ConcatenateMaps takes maps, not {r.ty.show}"
        match jt? with
        | none => jt? := some r.ty
        | some j =>
          let j' ← tryCatch (join a.pos j r.ty mapExp) (fun _ =>
            eerr a.pos s!"ConcatenateMaps takes maps of one type, not {j.show} and {r.ty.show}")
          jt? := some j'
        rs := rs.push r
      let some jt := jt? | eerr p "ConcatenateMaps takes at least one map"
      let .map kt vt := jt | eerr p s!"ConcatenateMaps takes maps, not {jt.show}"
      let tm ← fresh jt
      let some r0 := rs[0]? | eerr p "ConcatenateMaps takes at least one map"
      let mut code : Expr := .assign tm (← coerce a0.pos r0 jt)
      for (r, a) in rs.toList.tail.zip args.tail do
        let ts ← fresh jt
        let tpair ← fresh (.tup [kt, vt])
        let tk ← fresh kt
        let tv ← fresh vt
        let ti ← fresh .int
        let tidx ← fresh .int
        let put := Expr.seq (.assign tk (.prim (.tupGet 0) [.local tpair]))
          (.seq (.assign tv (.prim (.tupGet 1) [.local tpair])) (mapPut tm tk tv ti tidx))
        code := .seq code (.seq (.assign ts (← coerce a.pos r jt)) (.forE tpair (.local ts) (.lit (.logic true)) put))
      return ⟨.seq code (.local tm), jt⟩
    | "ToString" =>
      match args with
      | [a] => return ⟨← toStringOf p (← elabE ctx a none), Ty.string⟩
      | _ => eerr p "ToString takes one argument"
    | "Abs" =>
      -- (of a float, #127; each argument elaborated once)
      match args with
      | [a] =>
        let r ← elabE ctx a none
        if r.ty == .float then return ⟨.prim .fabs [r.e], .float⟩
        return ⟨.prim .abs [← coerce a.pos r .int], .int⟩
      | _ => eerr p "Abs takes one argument"
    | "Sqrt" | "Exp" | "Ln" | "Log" | "Pow" | "Sin" | "Cos" | "Tan" | "ArcSin" | "ArcCos" | "ArcTan"
    | "IsFinite" | "Sinh" | "Cosh" | "Tanh" | "ArSinh" | "ArCosh" | "ArTanh" | "Lerp" =>
      -- the mathematical functions of floats (#132); only IsFinite fails
      if name == "IsFinite" then needBracket name
      else if bracket then eerr p s!"{name} cannot fail: call it with {name}(…)"
      if ["Sinh", "Cosh", "Tanh", "ArSinh", "ArCosh", "ArTanh", "Lerp"].contains name then
        noteFx p ["reads"] (some name)
      let fl (a : SExpr) : EM Expr := do
        let r := widenR ctx.types (← elabE ctx a (some .float))
        if r.ty != .float then eerr a.pos s!"{name} takes floats, found {r.ty.show}"
        return r.e
      let unary : String → Option Prim
        | "Sqrt" => some .fsqrt | "Exp" => some .fexp | "Ln" => some .fln | "Sin" => some .fsin
        | "Cos" => some .fcos | "Tan" => some .ftan | "ArcSin" => some .fasin | "ArcCos" => some .facos
        | "ArcTan" => some .fatan | "IsFinite" => some .fisFinite
        | "Sinh" => some .fsinh | "Cosh" => some .fcosh | "Tanh" => some .ftanh
        | "ArSinh" => some .fasinh | "ArCosh" => some .facosh | "ArTanh" => some .fatanh
        | _ => none
      match name, args with
      | "Lerp", [a, b, parameter] =>
        let ta ← fresh .float
        let ea ← fl a
        let tb ← fresh .float
        let eb ← fl b
        let tp ← fresh .float
        let ep ← fl parameter
        let one := Expr.lit (.float 0x3FF0000000000000)
        let blend := p2 .fadd (p2 .fmul (.local ta) (p2 .fsub one (.local tp)))
          (p2 .fmul (.local tb) (.local tp))
        return ⟨.seq (.assign ta ea) (.seq (.assign tb eb) (.seq (.assign tp ep) blend)), .float⟩
      | "Pow", [a, b] => return ⟨p2 .fpow (← fl a) (← fl b), .float⟩
      | "ArcTan", [y, x] => return ⟨p2 .fatan2 (← fl y) (← fl x), .float⟩
      | "Log", [b, x] =>
        -- (`Log(Base, X)` is `Ln(X) / Ln(Base)`, the base evaluated first)
        let tb ← fresh .float
        let eb ← fl b
        let ex ← fl x
        return ⟨.seq (.assign tb eb) (p2 .fdiv (.prim .fln [ex]) (.prim .fln [.local tb])), .float⟩
      | n, [a] =>
        match unary n with
        | some op => return ⟨.prim op [← fl a], .float⟩
        | none => eerr p s!"{name} takes {if name == "Lerp" then "three" else "two"} floats"
      | _, _ => eerr p s!"{name} takes {if name == "Lerp" then "three floats" else if name == "Pow" || name == "Log" then "two floats" else if name == "ArcTan" then "one or two floats" else "one float"}"
    | "Round" | "Int" =>
      -- a float to an int (#127): `Round` ties to even, `Int` towards zero;
      -- failing on NaN, an infinity or out of range
      needBracket name
      match args with
      | [a] =>
        let r := widenR ctx.types (← elabE ctx a (some .float))
        if r.ty != .float then eerr p s!"{name} takes a float, found {r.ty.show}"
        return ⟨.prim (if name == "Round" then .fround else .ftrunc) [r.e], .int⟩
      | _ => eerr p s!"{name} takes one argument"
    | "Floor" | "Ceil" =>
      -- (of a float, #127: failable, so with brackets; of a rational or
      -- an int, with either, as the Book writes both)
      let ofFloat (r : R) : EM R := do
        if !bracket then eerr p s!"{name} of a float can fail: call it with {name}[…]"
        return ⟨.prim (if name == "Floor" then .ffloor else .fceil) [r.e], .int⟩
      match args with
      | [.bin bp "/" a b] =>
        let ra ← elabE ctx a none
        let rb ← elabE ctx b (if ra.ty == .float then some .float else none)
        if ra.ty == .float && rb.ty == .float then return ← ofFloat ⟨p2 .fdiv ra.e rb.e, .float⟩
        if ra.ty == .float || rb.ty == .float then
          eerr bp s!"no operator '/' for {ra.ty.show} and {rb.ty.show} (an int is not a float: write X * 1.0)"
        if ra.ty == .rational || rb.ty == .rational then
          eerr bp "'/' divides ints: openverse has no arithmetic on rationals (only Floor, Ceil and comparisons)"
        let es := [← coerce a.pos ra .int, ← coerce b.pos rb .int]
        return ⟨.prim (if name == "Floor" then .floorDiv else .ceilDiv) es, .int⟩
      | [e] =>
        -- (of a rational, #116: its denominator is positive, so this never
        -- fails; of an int, the int)
        let r := widenR ctx.types (← elabE ctx e none)
        match r.ty with
        | .int => return r
        | .float => ofFloat r
        | .rational =>
          let tr ← fresh .rational
          let tz ← fresh .int
          let op := if name == "Floor" then Prim.floorDiv else .ceilDiv
          let parts := [Expr.prim (.tupGet 0) [.local tr], .prim (.tupGet 1) [.local tr]]
          return ⟨.seq (.assign tr r.e) (Expr.orE tz (.prim op parts) (.lit (.int 0))), .int⟩
        | t => eerr p s!"{name} takes a rational or an int, found {t.show}"
      | _ => eerr p s!"{name} takes one argument"
    | "Quotient" => needBracket name; return ⟨.prim .quotient (← elabInts ctx p args), .int⟩
    | "Mod" => needBracket name; return ⟨.prim .modulo (← elabInts ctx p args), .int⟩
    | "Min" | "Max" =>
      -- (of floats, #127: NaN when either is)
      -- (each argument elaborated once)
      let [a, b] := args | eerr p s!"{name} takes two arguments"
      let ra ← elabE ctx a none
      let rb ← elabE ctx b (if ra.ty == .float || ra.ty == .int then some ra.ty else none)
      if ra.ty == .float then
        if rb.ty != .float then eerr p s!"{name} takes two floats or two ints, found float and {rb.ty.show}"
        return ⟨p2 (if name == "Min" then .fmin else .fmax) ra.e rb.e, .float⟩
      let es := [← coerce a.pos ra .int, ← coerce b.pos rb .int]
      let ta ← fresh .int
      let tb ← fresh .int
      let op := if name == "Min" then Prim.le else Prim.ge
      return ⟨.seq (.assign ta es[0]!) (.seq (.assign tb es[1]!)
        (.ite (p2 op (.local ta) (.local tb)) (.local ta) (.local tb))), .int⟩
    | "Err" =>
      modify fun st => if st.errAt.isNone then { st with errAt := some p } else st
      return ⟨.prim .userErr [], .never⟩
    | "$Show" =>
      -- the entry of `openverse run FILE do EXPR`: print the value when it
      -- has a ToString, else just evaluate it
      match args with
      | [a] =>
        let r ← elabE ctx a none
        match r.ty with
        | .int | .char | .float | .arr .char => return ⟨.print (← toStringOf p r), .void⟩
        | _ => return ⟨.seq r.e (.lit .void), .void⟩
      | _ => eerr p "internal: $Show"
    | _ =>
      -- `Sleep` (#156): the concurrency helpers' unless the program has its own
      let name := if name == "Sleep" && (ctx.sig? "Sleep").isNone then "$Sleep" else name
      if name == "$Sleep" && (ctx.sig? name).isNone then
        eerr p "Sleep suspends: it can only be called in a <suspends> function (#156)"
      match ctx.sig? name with
      | some s =>
        -- a call has its callee's effects
        noteFx p s.fx (some (if s.isConst then s!"uses the constant {name}" else s!"calls {name}"))
        if s.isConst then
          elabIndexLike ctx p ⟨.call s.idx [], s.ret⟩ args bracket
        else
          if s.decides && !bracket then eerr p s!"{name} is <decides>: call it with {name}[…]"
          -- the call syntax marks failure (Book of Verse §8.1)
          if !s.decides && bracket then eerr p s!"{name} cannot fail: call it with {name}(…)"
          if s.suspends then
            let shown := if name == "$EvAwait" then "Await"
              else if name.startsWith "$" then (name.drop 1).toString else name
            if !ctx.suspends then eerr p s!"{shown} suspends: it can only be called in a <suspends> function (#156)"
            if ctx.inDefer then eerr p s!"{shown} suspends, and a defer cannot suspend (#156)"
            if ctx.canFail then eerr p s!"{shown} suspends, and a failure context (a condition, a filter, or a <decides> call's arguments) cannot (#156)"
          if !s.tparams.isEmpty then
            let r ← elabGenericCall ctx p s args exp
            if s.suspends then return ⟨← withDeferMark ctx r.e, r.ty⟩ else return r
          let isNamed : SExpr → Bool
            | .decl _ n _ _ _ => n.startsWith "?"
            | _ => false
          -- (a suspension point records the defers active there, #156)
          let mark (e : Expr) : EM Expr := if s.suspends then withDeferMark ctx e else pure e
          if s.named.isEmpty && !args.any isNamed then
            -- a tuple for several parameters is expanded into them (Book of
            -- Verse ch. 3: `Describe(MyTuple)` is `Describe(1, "two")`)
            if let [a] := args then
              if s.params.length > 1 then
                let r ← elabE ctx a (some (.tup s.params))
                if let .tup ts := r.ty then
                  if ts.length == s.params.length then
                    let tt ← fresh r.ty
                    -- (an element that never gives a value left before the
                    -- call: `Err()` in its place, of every type, #290)
                    let parts ← ((s.params.zip ts).zip (List.range ts.length)).mapM fun ((pt, et), i) =>
                      if et == .never then pure (.prim .userErr [])
                      else coerce a.pos ⟨.prim (.tupGet i) [.local tt], et⟩ pt
                    return ⟨← mark (.seq (.assign tt r.e) (.call s.idx parts)), s.ret⟩
                let (shown, off) := match name.splitOn "." with
                  | [_, m] => if s.pnames.head? == some "Self" then (m, 1) else (name, 0)
                  | _ => (name, 0)
                eerr p s!"{shown} takes {s.params.length - off} argument(s), found 1 (of type {r.ty.show})"
            -- several arguments for one array parameter make the array
            -- (`Sum(1, 2, 3, 4)`, as a tuple converts to an array)
            if let [.arr et] := s.params then
              if args.length > 1 then
                let es ← elabArgs ctx p args (args.map fun _ => et)
                return ⟨← mark (.call s.idx [.prim .mkArr es]), s.ret⟩
            let es ← elabArgs ctx p args s.params
            return ⟨← mark (.call s.idx es), s.ret⟩
          -- named arguments: evaluate positional arguments left to right, then named ones as
          -- written, then the defaults of those omitted (Book of Verse §2.5), into temporaries
          let npos := s.params.length - s.named.length
          let pos := args.filter (!isNamed ·)
          let named := args.filterMap fun a => match a with
            | .decl ap n _ _ rhs => if n.startsWith "?" then some (ap, (n.drop 1).toString, rhs) else none
            | _ => none
          if pos.length != npos then
            -- a method's receiver is its first positional argument
            let (shown, off) := match name.splitOn "." with
              | [_, m] => (m, 1)
              | _ => (name, 0)
            eerr p s!"{shown} takes {npos - off} positional argument(s), found {pos.length - off}"
          for ((ap, n, _), i) in named.zip (List.range named.length) do
            if (s.named.find? (·.1 == n)).isNone then eerr ap s!"{name} has no parameter ?{n}"
            if (named.take i).any (·.2.1 == n) then eerr ap s!"?{n} is given twice"
          let ptys := s.params.toArray
          let mut steps : Array Expr := #[]
          let mut slots : Array (Option Nat) := Array.replicate s.params.length none
          for (a, k) in pos.zip (List.range npos) do
            let t := ptys[k]!
            let ta ← fresh t
            steps := steps.push (.assign ta (← coerce a.pos (← elabE ctx a (some t)) t))
            slots := slots.set! k (some ta)
          for (ap, n, rhs) in named do
            let k := npos + (s.named.findIdx? (·.1 == n)).get!
            let t := ptys[k]!
            let ta ← fresh t
            steps := steps.push (.assign ta (← coerce ap (← elabE ctx rhs (some t)) t))
            slots := slots.set! k (some ta)
          for ((n, dflt), j) in s.named.zip (List.range s.named.length) do
            let k := npos + j
            if slots[k]!.isNone then
              let some d := dflt | eerr p s!"{name} needs the argument ?{n}, which has no default"
              let t := ptys[k]!
              let ta ← fresh t
              -- (the default sees the parameters before it, in their temporaries)
              let earlier : List Local := ((s.pnames.zip (List.range k)).filterMap fun (pn, j) =>
                (slots[j]!).map fun sl => ({ name := pn, slot := sl, ty := ptys[j]!, mutable := false } : Local)).reverse
              -- (a method's: its receiver's fields too, through `Self`; a
              -- copy's in its interface's scope, as its body, #53)
              let selfC : Option String :=
                if s.pnames.head? == some "Self" then s.scope.orElse fun _ => (s.name.splitOn ".").head? else none
              -- (its own context: no return or break into the caller, failure
              -- only for a <decides> callee, and not its own default again)
              let key := (s.name, s!"?{n}")
              if ctx.defaults.contains key then
                eerr p s!"the default of ?{n} of {name} uses itself (a call of {name} that omits ?{n})"
              let dctx := { ctx with locals := earlier, selfClass := selfC,
                                     selfMethod := if selfC.isSome then (s.name.splitOn ".").getLast? else none,
                                     inParamDefault := true,
                                     inLoop := false, canFail := ctx.canFail && s.decides,
                                     suspends := ctx.suspends && s.suspends,
                                     defaults := key :: ctx.defaults }
              let rd ← fxAt p (do coerce p (← elabE dctx d (some t)) t)
              if !s.decides && rd.mayFail ctx.sigProg then
                eerr p s!"the default of ?{n} of {name} can fail, but {name} is not <decides>"
              steps := steps.push (.assign ta rd)
              slots := slots.set! k (some ta)
          let call := Expr.call s.idx (slots.toList.map fun o => Expr.local o.get!)
          let e := steps.toList.foldr Expr.seq call
          return ⟨← mark e, s.ret⟩
      | none =>
        if (ctx.sig? s!"{name}$init").isSome || (ctx.types.overloads.lookup s!"{name}$init").isSome then
          eerr p s!"{name} constructs an abstract class: it can only be delegated to, as {name}<constructor>(…) in a constructor of a class below it"
        eerr p s!"unknown function '{name}'"
  | .member mp (.ident _ "(super:)") m =>
    -- `(super:)M(…)`: the implementation the current method's class inherits
    let some c := ctx.selfClass | eerr p "(super:) can only be used in a method"
    if let some ms := (if (ctx.methodDecl? c m).isNone then ctx.types.methodOverloads.lookup m else none) then
      -- (the overloads above `c`)
      let above := (ctx.types.supers c).drop 1
      let declAbove (o : String) : Option String := above.find? fun e => (ctx.sig? s!"{e}.{o}").isSome
      let sigOf (o : String) : Option Sig := (declAbove o).bind fun owner =>
        (ctx.sig? s!"{owner}.{o}").map fun sg => { sg with params := sg.params.drop 1 }
      let vis := ms.filter fun o => (declAbove o).isSome
      if !vis.isEmpty then
        return ← resolveOverload ctx p m vis sigOf
          (fun o => elabApp ctx p (.member mp (.ident mp "(super:)") o) args bracket exp) args
    let impl ← superImpl ctx p c m
    elabApp ctx p (.ident mp impl) (.ident mp "Self" :: args) bracket exp
  | .member mp obj m0 =>
    let spawning := m0.startsWith "$spawnMethod:"
    let m0 := if spawning then (m0.drop 13).toString else m0
    -- `T.Await()` of a task (#156): the helper `$Await(T)`
    -- `T.Cancel()` of a task (#156): the mark `$cancelMark(T)`, which the
    -- lowering turns into the cancellation of the task's root
    if m0 == "Cancel" && args.isEmpty then
      let rt ← elabE ctx obj none
      if let .struct "task" [_] := rt.ty then
        if !ctx.suspends then eerr p "Cancel suspends: it can only be called in a <suspends> function (#156)"
        if ctx.inDefer then eerr p "Cancel suspends, and a defer cannot suspend (#156)"
        if ctx.canFail then eerr p "Cancel suspends, and a failure context (a condition, a filter, or a <decides> call's arguments) cannot (#156)"
        let some mark := ctx.sig? "$cancelMark" | eerr p "internal error: no Cancel helper"
        let t ← fresh rt.ty
        return ⟨.seq (.assign t rt.e) (.call mark.idx [.local t]), .void⟩
    -- `E.Signal()` of an `event()` (#156): with the value `void`
    if m0 == "Signal" && args.isEmpty then
      match (← elabE ctx obj none).ty with
      | .struct "event" [.void] | .struct "sticky_event" [.void] | .struct "$subev0" [] =>
        return ← elabApp ctx p (.member mp obj "Signal") [.tuple p []] bracket exp
      | _ => pure ()
    if m0 == "Await" && args.isEmpty then
      match (← elabE ctx obj none).ty with
      | .struct "task" [_] => return ← elabApp ctx p (.ident mp "$Await") [obj] false exp
      | .struct "event" [_] | .struct "subscribable_event" [_] | .struct "$subev0" [] =>
        return ← elabApp ctx p (.ident mp "$EvAwait") [obj] false exp
      | .struct "sticky_event" [_] => return ← elabApp ctx p (.ident mp "$StickyAwait") [obj] false exp
      | _ => pure ()
    let r0 ← elabE ctx obj none
    -- `X.(i:)M(…)`: `X` as an `i`, so `i`'s `M` (a qualified call)
    let (r, m) ← match r0.ty, m0.startsWith "(", (m0.drop 1).toString.splitOn ":)" with
      | .struct c ts, true, [q, mq] =>
        if !(ctx.types.isSub c q) then eerr p s!"{c} is not below {q}"
        -- (converted: a receiver of a type with no instance is unreachable)
        let qt : Ty := .struct q (ctx.types.upArgs c ts q)
        pure (⟨← coerce p r0 qt, qt⟩, mq)
      | _, _, _ => pure (r0, m0)
    match r.ty with
    | .struct c targs =>
      let env := ctx.types
      -- an overloaded method (#106): the overload visible at `c` the call
      -- fits, then that method
      if let some ms := (if env.classes.contains c && (ctx.methodDecl? c m).isNone then
          env.methodOverloads.lookup m else none) then
        let sigOf (o : String) : Option Sig := (ctx.methodDecl? c o).bind fun owner =>
          (ctx.sig? s!"{owner}.{o}").map fun sg => { sg with params := sg.params.drop 1 }
        let vis := ms.filter fun o => (ctx.methodDecl? c o).isSome
        -- (a qualified call stays qualified: `X.(q:)M$ovK(…)`, #125)
        let qualOf (o : String) : String :=
          if m0.startsWith "(" then
            match (m0.drop 1).toString.splitOn ":)" with
            | [q, _] => s!"({q}:){o}"
            | _ => o
          else o
        if !vis.isEmpty then
          return ← resolveOverload ctx p m vis sigOf (fun o => elabApp ctx p (.member mp obj ((if spawning then "$spawnMethod:" else "") ++ qualOf o)) args bracket exp) args
      if let (true, some owner) := (env.classes.contains c, ctx.methodDecl? c m) then
        -- the slots the call covers (#70): every class below `c` must implement
        -- them alike, or the call must say which
        let roots := ctx.rootsOf c m
        let root := roots.headD owner
        for d in env.concreteBelow c do
          for o in roots do
            if ctx.implFor? d o m != ctx.implFor? d root m then
              eerr p s!"{d} implements {m} separately for {root} and {o}: call it as X.({root}:){m}(…) or X.({o}:){m}(…)"
        let ms := (ctx.sig? s!"{owner}.{m}").get!
        if spawning && !ms.suspends then
          eerr p "spawn{…} takes a call of a <suspends> function (#156)"
        if ms.decides && !bracket then eerr p s!"{m} is <decides>: call it with {m}[…]"
        if !ms.decides && bracket then eerr p s!"{m} cannot fail: call it with {m}(…)"
        if ms.named.isEmpty && args.length + 1 != ms.params.length then
          eerr p s!"{m} takes {ms.params.length - 1} argument(s), found {args.length}"
        let slot ← fresh r.ty
        let recv := s!"$recv{slot}"
        let ds := env.concreteBelow c
        -- one implementation for every class below the receiver's type, above
        -- that type: a direct call (the receiver evaluated first, as `Self`)
        let clsOf (fname : String) : String := (fname.splitOn ".").head!
        let direct : Option String := match (ds.map (ctx.implFor? · root m)).eraseDups with
          | [some fname] => if env.isSub c (clsOf fname) then some fname else none
          | _ => none
        -- the receiver as an instance of class `e`, above or below `c` (#39)
        let argsAt (e : String) : List Ty :=
          if env.isSub c e then env.upArgs c targs e else env.argsBelow c targs e
        if let some fname := direct then
          let e := clsOf fname
          let ctx' := { ctx with locals := { name := recv, slot, ty := .struct e (argsAt e), mutable := false } :: ctx.locals }
          let rc ← if spawning then
              elabSpawn ctx' p (.app p (.ident mp fname) (.ident mp recv :: args) bracket)
            else elabApp ctx' p (.ident mp fname) (.ident mp recv :: args) bracket exp
          return ⟨.seq (.assign slot r.e) rc.e, rc.ty⟩
        -- otherwise dispatch on the class of the receiver's value: the
        -- receiver, then the arguments, once each, then the implementation of
        -- the class whose option is set
        let ownerTps := ((env.sparams.lookup owner).getD []).map (·.1)
        -- the declaration's types at the receiver's type arguments, its own
        -- type parameters renamed apart (they are inferred from the
        -- arguments below, as for a generic call)
        let ownTps := ms.tparams.drop ownerTps.length
        let ownσ : List (String × Ty) := (ownTps.zip (List.range ownTps.length)).map fun ((v, k), i) =>
          (v, Ty.param s!"$own{i}" k)
        let ownNames := (List.range ownTps.length).map fun i => s!"$own{i}"
        let σ := ownerTps.zip (argsAt owner)
        let declTy (t : Ty) : Ty := (t.subst ownσ).subst σ
        let mut σu : List (String × Ty) := []
        -- the arguments, once each: positional ones left to right, then named
        -- ones as written (Book of Verse §2.5), passed to every implementation;
        -- those omitted take the default of the implementation that runs, as
        -- in a call without named arguments
        let isNamed : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
        let posArgs := args.filter (!isNamed ·)
        let namedArgs := args.filterMap fun a => match a with
          | .decl ap n _ _ rhs => if n.startsWith "?" then some (ap, (n.drop 1).toString, rhs) else none
          | _ => none
        let npos := ms.params.length - ms.named.length
        if posArgs.length + 1 != npos then
          eerr p s!"{m} takes {npos - 1} positional argument(s), found {posArgs.length}"
        for (ap, n, _) in namedArgs do
          if (ms.named.find? (·.1 == n)).isNone then eerr ap s!"{m} has no parameter ?{n}"
        let mut pre : Array Expr := #[.assign slot r.e]
        let mut locs : List Local := [{ name := recv, slot, ty := r.ty, mutable := false }]
        let mut argIds : Array SExpr := #[]
        -- the method's own type parameters, from the expected result type
        -- (unless void), then from the arguments, as for a generic call: an
        -- argument is checked against its parameter's type once the own type
        -- parameters it mentions are bound, else inferred from; `false`,
        -- `array{}` and `map{}` take their type from context, so they wait
        -- for the others (they are still evaluated in order)
        let showT (t : Ty) : String :=
          (t.subst ((ownNames.zip ownTps).map fun (n, (v, k)) => (n, Ty.param v k))).show
        let own? (σ' : List (String × Ty)) := σ'.filter fun (v, _) => ownNames.contains v
        if let some et := exp then
          if !(et == .void) then
            if let some σ' := (declTy ms.ret).matchArg ctx.types σu et then σu := own? σ'
        -- Infer from all given arguments before checking contextual values,
        -- preserving positional then written named order in the emitted code.
        let given : List (SExpr × Ty × Option String) :=
          (posArgs.zip ((ms.params.drop 1).take (npos - 1))).map (fun (a, t) => (a, t, none)) ++
          namedArgs.map (fun (_, n, rhs) =>
            (rhs, ms.params[npos + (ms.named.findIdx? (·.1 == n)).get!]!, some n))
        let contextual := (← given.mapM (fun (a, _, _) => argNeedsTypeWith elabE ctx a)).toArray
        let mut done : Array (Option (Expr × Ty)) := Array.replicate given.length none
        let mut deferred : Array Bool := contextual
        for pass in [0, 1] do
          for ((a, t0, _), i) in given.zipIdx do
            if (pass == 0) == deferred[i]! then continue
            let t := (declTy t0).subst σu
            if t.params.any ownNames.contains then
              if contextual[i]! then
                eerr a.pos s!"cannot infer the type parameters of {m} from the arguments of this call"
              let r ← elabE ctx a none
              match t.matchArg ctx.types σu r.ty with
              | some σ' =>
                σu := own? σ'
                let t' := t.subst σu
                if t'.params.any ownNames.contains then
                  if pass == 0 then deferred := deferred.set! i true
                  else eerr a.pos s!"cannot infer the type parameters of {m} from this argument"
                else done := done.set! i (some (← coerce a.pos r t', t'))
              | none => eerr a.pos s!"expected {showT t}, found {r.ty.show} (in a call of {m})"
            else
              done := done.set! i (some (← coerce a.pos (← elabE ctx a (some t)) t, t))
        let mut namedSlots : List (String × Nat) := []
        for ((_, _, name), d) in given.zip done.toList do
          let some (e, t) := d | eerr p s!"cannot infer the type parameters of {m} from the arguments of this call"
          let ta ← fresh t
          pre := pre.push (.assign ta e)
          locs := { name := s!"$arg{ta}", slot := ta, ty := t, mutable := false } :: locs
          match name with
          | none => argIds := argIds.push (.ident mp s!"$arg{ta}")
          | some n => namedSlots := namedSlots ++ [(n, ta)]
        for (n, ta) in namedSlots do
          argIds := argIds.push (.decl mp s!"?{n}" none false (.ident mp s!"$arg{ta}"))
        let msRet := (declTy ms.ret).subst σu
        if msRet.params.any ownNames.contains then
          eerr p s!"cannot infer the type parameters of {m} from the arguments of this call"
        if spawning then
          let isS (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.suspends
          let skip (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.name == "$spawnMark"
          if pre.any (fun e => Suspend.countSusp isS (fun _ => false) false skip e > 0) then
            eerr p "the arguments of a spawned call cannot suspend (#156)"
          let taskTy := Ty.struct "task" [msRet]
          let rargs := env.coreArgs c targs
          let mut acc : Expr := .prim .userErr []
          for d in ds.reverse do
            let some fname := ctx.implFor? d root m | eerr p s!"class {d} does not implement '{m}'"
            let vars := env.coreVars d
            let X := vars.zipIdx.map fun ((_, t), i) =>
              Ty.param s!"$ext{i}" (match t with | .param _ k => k | _ => false)
            let view := if env.viewed.contains c then env.viewOf c d X else X.take rargs.length
            let atX := X.zipIdx.map fun (x, j) => (pinArg j, x)
            let pins := (X.zip (env.corePins d)).filterMap fun (x, pin) =>
              pin.map fun t => (x, t.subst atX)
            let fields (n : String) (ts : List Ty) : Option (List Ty) :=
              if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
            let some mu := Ty.unifyEqs fields [] (view.zip rargs ++ pins) | continue
            let dargs := ((env.sparams.lookup d).getD []).map fun (n, _) =>
              (vars.findIdx? (·.1 == n)).map (X[·]!) |>.getD .void
            let some mu := env.refineComparable? mu (env.comparableArgs d dargs) | continue
            let name := s!"$spawnSelf{slot}"
            let self : Local := { name, slot, ty := .struct d (dargs.map (·.subst mu)), mutable := false }
            let unrefine := mu.filterMap fun (n, t) =>
              if ctx.dictVars.contains n && t.params.any (·.startsWith "$ext") then
                (env.tvars.lookup n).map (t, ·) else none
            let cctx := { ctx with
              locals := self :: (locs ++ ctx.locals).map (fun l => { l with ty := l.ty.subst mu }),
              types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst mu) }, unrefine }
            let rc ← elabSpawnDispatch cctx p d fname s!"{owner}.{m}" (.ident p name :: argIds.toList)
              (some (taskTy.subst mu))
            match rc.e with
            | .prim .userErr [] => continue -- factory discovery; no task or wait yet
            | _ => pure ()
            let some (.call fi (.local receiver :: values)) := Expr.inlineArgTemps rc.e
              | eerr p "internal: a spawn factory is not a dispatch call"
            if receiver != slot then eerr p "internal: a spawn factory changed its receiver"
            acc := .ite (.heap (.isTag [env.tagOf d]) [.local slot]) (.call fi (.local slot :: values)) acc
          let result ← fresh taskTy
          return ⟨pre.toList.foldr Expr.seq (.assign result acc), taskTy⟩
        let mut acc : Expr := .prim .userErr []   -- no option set: unreachable
        -- Supplied arguments have already been evaluated in caller order.
        -- Default forwarding leaves only those typed locals in the dispatch.
        if env.viewed.contains c then
          -- (#351) a receiver through views: one test per class below, a
          -- dispatch that opens the class's Verse Core type arguments,
          -- refined by its view (the receiver's are the interface's at the
          -- class's) and its pins (`Typed.dispatch_view`)
          let rargs := env.coreArgs c targs
          let mut emitted := false
          for d in ds.reverse do
            let some fname := ctx.implFor? d root m | eerr p s!"class {d} does not implement '{m}'"
            let e := clsOf fname
            let vars := env.coreVars d
            -- (each as comparable as the type parameter at its place)
            let X := vars.zipIdx.map fun ((_, t), i) =>
              Ty.param s!"$ext{i}" (match t with | .param _ k => k | _ => false)
            let view := env.viewOf c d X
            let atX := X.zipIdx.map fun (x, j) => (pinArg j, x)
            let pinEqs := (X.zip (env.corePins d)).filterMap fun (x, pin) => match pin with
              | some pt => some (x, pt.subst atX)
              | none => none
            let coreFields (n : String) (ts : List Ty) : Option (List Ty) :=
              if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
            -- (no substitution relates them: no object of `d` is the receiver)
            -- (the opened ones bound to the reference's, not those to them:
            -- the code's own type parameters keep their names, as in a
            -- dispatch with no view, and errors name them)
            let some μF := Ty.unifyEqs coreFields [] (view.zip rargs ++ pinEqs) | continue
            let selfName := s!"$self{slot}"
            -- (the implementation's class or interface `e`, above `d`, at
            -- its places among the opened ones: a class's are a prefix of
            -- `d`'s, an interface's those its view gives; not through `d`'s
            -- own parameters, which a class that only inherits has no pins
            -- relating to them, `low(t, u) := class(both(t, []u))`)
            let eCore : List Ty := if env.viewed.contains e then env.viewOf e d X else X
            let eVars := env.coreVars e
            let eArgs := ((env.sparams.lookup e).getD []).map fun (v, _) =>
              match eVars.findIdx? (fun (x : String × Ty) => x.1 == v) with
              | some j => eCore.getD j Ty.void
              | none => Ty.void
            let some μF := env.refineComparable? μF (env.comparableArgs e eArgs) | continue
            let locsF := locs.map fun l => { l with ty := l.ty.subst μF }
            let selfL : Local := { name := selfName, slot,
                                   ty := .struct e (eArgs.map (·.subst μF)), mutable := false }
            let unrefine := μF.filterMap fun (x, t) =>
              if ctx.dictVars.contains x && t.params.any (·.startsWith "$ext") then
                (ctx.types.tvars.lookup x).map (t, ·)
              else none
            let ctx' := { ctx with
              locals := selfL :: (locsF ++ ctx.locals.map fun l => { l with ty := l.ty.subst μF }),
              types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst μF) }, unrefine }
            let rc ← elabDefaultDispatch ctx' p fname (.ident mp selfName :: argIds.toList) bracket
              (some (msRet.subst μF))
            let rcE : Expr := match rc.e with
              | .seq (.ite (.prim .fail []) _ (.lit .void)) b => b
              | e => e
            -- (a dispatch through a view opens all of the class's type
            -- arguments: defaults with no type of their own at the
            -- declaration's, #209)
            let some (.call fi (.local s0 :: es)) := Expr.inlineArgTemps rcE
              | eerr p s!"cannot dispatch {m} through a view to class {d} yet when a named argument's default is computed (#351)"
            if s0 != slot then eerr p s!"internal error: a dispatch through a view to class {d} (#351)"
            acc := .ite (.heap (.isTag [env.tagOf d]) [.local slot]) (.call fi (.local slot :: es)) acc
            emitted := true
          if !emitted && ms.decides then acc := .prim .fail []
          let y ← fresh msRet
          let body ← if ms.suspends then withDeferMark ctx (.assign y acc) else pure (.assign y acc)
          return ⟨pre.toList.foldr Expr.seq body, msRet⟩
        if env.isRefClass c then
          -- a reference: one test of the object's class per implementation (#34)
          let mut groups : Array (String × Array String) := #[]
          for d in ds do
            let some fname := ctx.implFor? d root m | eerr p s!"class {d} does not implement '{m}'"
            match groups.findIdx? (·.1 == fname) with
            | some gi => groups := groups.modify gi fun (e', cls) => (e', cls.push d)
            | none => groups := groups.push (fname, #[d])
          let mut pinned := false
          let mut emitted := false
          for (fname, cls) in groups.toList.reverse do
            let e := clsOf fname
            -- (#142) the type arguments the classes fix that the receiver's
            -- may not have: matched against the receiver's, they refine the
            -- call, which `Typed.dispatch` types under that refinement
            let rargs := env.coreArgs c targs
            -- (#209) the type arguments that the tested classes have pins
            -- on beyond the receiver's are opened as fresh parameters, which
            -- the refinement binds (as the checker opens them, `openCount`:
            -- a test is of classes with the same pins)
            let eLen := (env.pinsOf e).length
            let extOf (pins : List (Option Ty)) : List Ty :=
              (List.range (pins.length - rargs.length)).map fun i => Ty.param s!"$ext{i}" false
            let needOf (pins : List (Option Ty)) :=
              let rx := rargs ++ extOf pins
              let atR := rx.zipIdx.map fun (r, j) => (pinArg j, r)
              (rx.zip pins).filterMap fun (a, pin) => match pin with
                | some pt => let pt := pt.subst atR; if a == pt then none else some (a, pt)
                | none => none
            -- (a generic <suspends> implementation at or above the receiver's
            -- class is called at the receiver's own type arguments, without
            -- the refinement: its frame is made by a call typed without it)
            let plainSusp := ms.suspends && env.isSub c e && !((ctx.sig? fname).map (·.tparams.isEmpty)).getD true
            -- (an implementation at or above the receiver's class is called
            -- at the receiver's type arguments, which it takes as they are)
            if !plainSusp && !env.isSub c e && cls.any fun d =>
                !(needOf (env.corePins d)).isEmpty || eLen > rargs.length then
              -- one test per set of pins among the classes using `e`'s
              -- implementation: `Typed.dispatch` refines by the pins all the
              -- tested classes share, which may fix more than `e`'s (and it
              -- takes the receiver as narrowed by the test, so no temporary
              -- of `e`'s type, which might have no initial value)
              let mut parts : Array (List (Option Ty) × Array String) := #[]
              for d in cls do
                -- (by their Verse Core pins, which the rule compares, #351)
                let key := env.dispatchPins d
                match parts.findIdx? (·.1 == key) with
                | some pi => parts := parts.modify pi fun (k, ds') => (k, ds'.push d)
                | none => parts := parts.push (key, #[d])
              for (pins, part) in parts.toList.reverse do
                -- (whether an object of `part` can be the receiver, by
                -- Verse's types)
                if (Ty.unifyEqs (fun _ _ => none) [] (needOf pins)).isNone then continue
                -- (pins that relate the receiver's type arguments to ones
                -- past those of `e`, whose implementation is called: they
                -- would instantiate `e`'s type parameters with what the
                -- dispatch opens; so, where `e` takes the receiver's type
                -- arguments as they are (no pins of its own on them, and no
                -- more of them), no refinement, and `e`'s implementation
                -- takes the receiver as it is; elsewhere the refinement
                -- below, whose hidden arguments for `e`'s implementation are
                -- built from the caller's own type parameters, which the
                -- refinement binds to what it opens, `Ctx.unrefine`, #209)
                -- (unless the implementation takes no values of type arguments,
                -- reading them from its receiver, `Sig.selfTps`)
                let calleeDicts := ((ctx.sig? fname).map (·.ndicts)).getD 0
                if calleeDicts != 0 &&
                    !VTy.pinsBelow (env.lowerPins (pins.take (max eLen rargs.length))) (max eLen rargs.length) &&
                    (needOf (env.corePins e)).isEmpty && eLen ≤ rargs.length then
                  let argsE := argsAt e
                  let some μ := env.refineComparable? [] (env.comparableArgs e argsE) | continue
                  let ty := Ty.struct e (argsE.map (·.subst μ))
                  let sd ← fresh ty
                  let ctx' := { ctx with
                    locals := { name := s!"$self{sd}", slot := sd, ty, mutable := false } ::
                      ((locs ++ ctx.locals).map fun l => { l with ty := l.ty.subst μ }),
                    types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst μ) } }
                  let rc ← elabApp ctx' p (.ident mp fname) (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
                  acc := .ite (.assign sd (.heap (.isTag (part.toList.map env.tagOf)) [.local slot]))
                    (← coerce p rc msRet) acc
                  emitted := true
                  continue
                -- (no instance of the receiver's type arguments agrees with
                -- the pins: no object of `part` is the receiver)
                -- (whether an object of `part` can be the receiver, by
                -- Verse's types; the refinement, as Verse Core has it: a
                -- value struct by its fields, #209)
                if (Ty.unifyEqs (fun _ _ => none) [] (needOf pins)).isNone then continue
                let coreFields (n : String) (ts : List Ty) : Option (List Ty) :=
                  if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
                let some μF := Ty.unifyEqs coreFields [] (needOf pins) | continue
                let selfName := s!"$self{slot}"
                let argsE := if env.isSub c e then argsAt e else env.argsBelow c targs e (extOf pins)
                let some μF := env.refineComparable? μF (env.comparableArgs e argsE) | continue
                let locsF := locs.map fun l => { l with ty := l.ty.subst μF }
                let selfL : Local := { name := selfName, slot, ty := .struct e (argsE.map (·.subst μF)), mutable := false }
                -- (the caller's type parameters the refinement binds to
                -- types that mention opened ones, for the hidden arguments
                -- of a generic implementation, #209)
                let unrefine := μF.filterMap fun (x, t) =>
                  if ctx.dictVars.contains x && t.params.any (·.startsWith "$ext") then
                    (ctx.types.tvars.lookup x).map (t, ·)
                  else none
                let ctx' := { ctx with
                  locals := selfL :: (locsF ++ ctx.locals.map fun l => { l with ty := l.ty.subst μF }),
                  types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst μF) }, unrefine }
                let rc ← elabDefaultDispatch ctx' p fname (.ident mp selfName :: argIds.toList) bracket
                  (some (msRet.subst μF))
                -- (named arguments go through temporaries: put their values
                -- in the call, which must have the rule's shape)
                -- (a suspends call carries the defers active at it, which
                -- go around the whole dispatch instead)
                let rcE : Expr := match rc.e with
                  | .seq (.ite (.prim .fail []) _ (.lit .void)) b => b
                  | e => e
                let some (.call fi (.local s0 :: es)) := Expr.inlineArgTemps rcE
                  | eerr p s!"cannot dispatch {m} to class {e}, which fixes type arguments of {c}, when a named argument's default is computed (#142)"
                if s0 != slot then eerr p s!"cannot dispatch {m} to class {e}, which fixes type arguments of {c} (#142)"
                acc := .ite (.heap (.isTag (part.toList.map env.tagOf)) [.local slot]) (.call fi (.local slot :: es)) acc
                pinned := true
                emitted := true
              continue
            let argsE := argsAt e
            let some μ := env.refineComparable? [] (env.comparableArgs e argsE) | continue
            let ty := Ty.struct e (argsE.map (·.subst μ))
            let sd ← fresh ty
            let ctx' := { ctx with
              locals := { name := s!"$self{sd}", slot := sd, ty, mutable := false } ::
                ((locs ++ ctx.locals).map fun l => { l with ty := l.ty.subst μ }),
              types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst μ) } }
            let rc ← elabApp ctx' p (.ident mp fname) (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
            acc := .ite (.assign sd (.heap (.isTag (cls.toList.map env.tagOf)) [.local slot]))
              (← coerce p rc msRet) acc
            emitted := true
          -- (no class can be the receiver: the call cannot run; a failable
          -- one still fails, for the failure checks)
          if !emitted && ms.decides then acc := .prim .fail []
          if pinned then
            -- (checked against the method's result type, as the refined
            -- calls need an expected type)
            let y ← fresh msRet
            let body ← if ms.suspends then withDeferMark ctx (.assign y acc) else pure (.assign y acc)
            return ⟨pre.toList.foldr Expr.seq body, msRet⟩
          return ⟨pre.toList.foldr Expr.seq acc, msRet⟩
        for (d, j) in (ds.zip (List.range ds.length)).reverse do
          let some fname := ctx.implFor? d root m | eerr p s!"class {d} does not implement '{m}'"
          let td ← fresh (classRepTy env d)
          let sd ← fresh (.struct d [])
          let ctx' := { ctx with locals := { name := s!"$self{sd}", slot := sd, ty := .struct d [], mutable := false } :: (locs ++ ctx.locals) }
          let rc ← elabApp ctx' p (.ident mp fname) (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
          acc := .ite (.assign td (.prim .query [.prim (.tupGet j) [.local slot]]))
            (.seq (.assign sd (classWrap env d d (.local td))) (← coerce p rc msRet)) acc
        let y ← fresh msRet
        return ⟨pre.toList.foldr Expr.seq (.assign y acc), msRet⟩
      else if (ctx.types.fields c targs).any (·.1 == m) then
        -- `S.F[i]`, `S.F(k)`: a field, indexed
        elabIndexLike ctx p (← elabMember ctx p r m) args bracket
      else if ctx.types.classes.contains c then eerr p s!"class {c} has no method '{m}'"
      else eerr p s!"struct {c} has no field '{m}' (structs have no methods)"
    | _ => elabMethod ctx p r m args bracket
  | _ => elabIndexLike ctx p (← elabE ctx f none) args bracket

/-- `T[X]`: `X` as a value of class or interface `T`, failing unless its class
    is below `T`; `T(X)`: an upcast, which cannot fail (Book of Verse ch. 10). -/
partial def elabCast (ctx : Ctx) (p : Pos) (T : String) (args : List SExpr) (bracket : Bool) : EM R := do
  let env := ctx.types
  let [a] := args | eerr p s!"a cast {T}[X] takes one value"
  let r ← elabE ctx a none
  let (S, sargs) ← match r.ty with
    | .struct S sargs => if env.classes.contains S then pure (S, sargs) else eerr p s!"cannot cast {withArticle S} to {T}"
    | t => eerr p s!"cannot cast {withArticle t.show} to {T}"
  -- (#351) from a reference through views, a cast to a class or interface
  -- with Verse Core type arguments takes them from a dispatch: as the first
  -- clause of an if's condition, whose branch is a function of its own
  if bracket && env.viewed.contains S && !(env.coreArgs T (((env.sparams.lookup T).getD []).map fun (v, k) => Ty.param v k)).isEmpty then
    let what := s!"a cast of {withArticle r.ty.show}, an interface referred to through views, to {T}"
    if !(env.isSub S T || env.isSub T S) then
      eerr p s!"{what}, which is neither above nor below {S}, is not supported yet (#351)"
    if env.isSub S T then
      eerr p s!"{what}, which is above {S}, cannot fail: use {T}(…), an upcast (#351)"
    -- (no class below both whose view and pins can give the object's type
    -- arguments: it would always fail, as main says of a positional one)
    if ((env.concreteBelow S).filter (env.isSub · T)).all fun d =>
        (env.viewArgs? S d (env.coreArgs S sargs) (rigid := false)).isNone then
      eerr p s!"{withArticle r.ty.show} is never {withArticle T}: no class below both gives {S} those type arguments, so {T}[…] would always fail"
    -- (one the first clause of an if's condition does not take either: an
    -- interface whose type arguments the cast would open, #53)
    if (refiningCast? env T r.ty).isNone then
      eerr p s!"{what} would leave {T}'s type arguments unknown: they are not {S}'s, and an interface has no hidden fields to read them from (#351, #53)"
    let theirs := if (env.sparams.lookup T).isNone then s!"the type arguments {T} fixes" else s!"{T}'s type arguments"
    eerr p s!"{what} works only as the first clause of an if's condition, D := {T}[X], whose branch then has {theirs} (#351)"
  -- a parametric class's type arguments are those of the value (#39), in the
  -- same hierarchy
  let parametric := (env.sparams.lookup T).isSome || !(env.coreArgs T []).isEmpty
  if (env.concreteBelow S).all (fun d => !env.isSub d T) then
    eerr p s!"no class is below both {r.ty.show} and {T}, so {T}[…] would always fail"
  if parametric && !(env.isSub S T || env.isSub T S) then
    eerr p s!"cannot cast {withArticle S} to {T}: {T}'s type arguments would be unknown (they are not {S}'s)"
  let targs := if env.isSub S T then env.upArgs S sargs T else env.argsBelow S sargs T
  if parametric && (env.coreArgs T targs).length > (env.coreArgs S sargs).length then
    eerr p s!"cannot cast {withArticle r.ty.show} to {T}: {T} has type parameters that {S} does not have, which would be unknown here: a cast opens them only as the first clause of an if's condition, D := {T}[X], whose branch then has them (#250)"
  if bracket then
    match env.refineComparable? [] (env.comparableArgs T targs) with
    | none => eerr p s!"{withArticle r.ty.show} is never {withArticle T}: its type arguments do not satisfy {T}'s comparable bounds"
    | some μ =>
      if !μ.isEmpty then
        eerr p s!"a cast to {T} strengthens comparable bounds, which works only as the first clause of an if's condition, D := {T}[X] (#209)"
  let tty : Ty := .struct T targs
  if !bracket then
    if !env.isSub S T then
      eerr p s!"{T}(…) converts to a supertype, and {S} is not below {T}: use {T}[…] to cast down"
    return ⟨← coerce p r tty, tty⟩
  let below := env.concreteBelow S
  let common := below.filter (env.isSub · T)
  if common.isEmpty then
    eerr p s!"no class is below both {r.ty.show} and {T}, so {T}[…] would always fail"
  if parametric && env.coreArgs T targs != env.coreArgs S sargs then
    if (Ty.unifyEqs (fun _ _ => none) [] ((env.coreArgs S sargs).zip (env.coreArgs T targs))).isSome then
      eerr p s!"cannot cast {withArticle r.ty.show} to {(Ty.struct T targs).show} here: their type arguments agree only under a refinement, which a cast gives only as the first clause of an if's condition, D := {T}[X], whose branch is then typed under it (#209, #243)"
    -- (in a class's copy of an interface's default, at type arguments the
    -- class fixes, it fails, as the interface's own default's would, #53)
    if !ctx.liftTag.isEmpty then return ⟨.prim .fail [], tty⟩
    eerr p s!"{withArticle r.ty.show} is never {withArticle T}: their type arguments differ, so {T}[…] would always fail"
  -- a reference: a test of its object's class (#34)
  if env.isRefClass S then return ⟨.heap (.isTag (common.map env.tagOf)) [r.e], tty⟩
  let x ← fresh r.ty
  let mut acc : Expr := .prim .fail []
  for d in common.reverse do
    let j := (below.idxOf? d).getD 0
    let td ← fresh (classRepTy env d)
    acc := .ite (.assign td (.prim .query [.prim (.tupGet j) [.local x]])) (classWrap env T d (.local td)) acc
  let y ← fresh (.struct T [])
  return ⟨.seq (.assign x r.e) (.assign y acc), .struct T []⟩

/-- `elabRefinedIfWith`, given this block's functions (#325). -/
partial def elabRefinedIf (ctx : Ctx) (p _dp : Pos) (D T : String) (x : SExpr) (body0 : SExpr)
    (elseE : Option SExpr) (exp : Option Ty) (made : Bool := false) : EM (Option R) :=
  elabRefinedIfWith elabApp elabE withDeferMark ctx p _dp D T x body0 elseE exp made

/-- `elabGenericCallWith`, given this block's functions (#325). -/
partial def elabGenericCall (ctx : Ctx) (p : Pos) (s : Sig) (args : List SExpr) (exp : Option Ty) :
    EM R :=
  elabGenericCallWith elabE ctx p s args exp

/-- The failable array methods of the Book of Verse (§9.1):
    `A.Slice[i, j]`, `A.Slice[i]`, `A.Find[x]`, `A.RemoveElement[i]`,
    `A.ReplaceElement[i, x]`, `A.Insert[i, B]`, `A.Last[]`, `A.Last[n]`. Each fails when an index is
    out of range (or, for `Find`, when there is no such element). -/
partial def elabMethod (ctx : Ctx) (p : Pos) (r : R) (m : String) (args : List SExpr) (bracket : Bool) :
    EM R := do
  let .arr t := r.ty | eerr p s!"{r.ty.show} has no method '{m}'"
  -- (the methods that cannot fail take parentheses, #150)
  let total := ["RemoveAllElements", "ReplaceAllElements", "ReplaceAll"].contains m
  if total && bracket then eerr p s!"{m} cannot fail: call it with A.{m}(…)"
  if !total && !bracket then eerr p s!"{m} can fail: call it with A.{m}[…]"
  let ta ← fresh r.ty
  let len := Expr.prim .len [.local ta]
  let int (i : Int) : Expr := .lit (.int i)
  -- the elements of A at indices lo, …, hi - 1 (lo ≤ hi known)
  let slice (lo hi : Expr) : EM Expr := do
    let ti ← fresh .int
    let tx ← fresh t
    return .forE ti (.prim .range [lo, p2 .sub hi (int 1)]) (.assign tx (p2 .index (.local ta) (.local ti)))
      (.local tx)
  let start := Expr.assign ta r.e
  match m, args with
  | "Slice", [a, b] =>
    let es ← elabInts ctx p [a, b]
    let tlo ← fresh .int
    let thi ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tlo)) (.seq (p2 .le (.local tlo) (.local thi))
      (p2 .le (.local thi) len))
    return ⟨.seq start (.seq (.assign tlo es[0]!) (.seq (.assign thi es[1]!) (.seq chk
      (← slice (.local tlo) (.local thi))))), r.ty⟩
  | "Slice", [a] =>
    let es ← elabInts ctx p [a]
    let tlo ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tlo)) (p2 .le (.local tlo) len)
    return ⟨.seq start (.seq (.assign tlo es[0]!) (.seq chk (← slice (.local tlo) len))), r.ty⟩
  | "Find", [x] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t "the element type of Find")
    let rx ← elabE ctx x (some t)
    let tx ← fresh t
    let ti ← fresh .int
    let found := Expr.forE ti (.prim .range [int 0, p2 .sub len (int 1)])
      (p2 .eq (p2 .index (.local ta) (.local ti)) (.local tx)) (.local ti)
    return ⟨.seq start (.seq (.assign tx (← coerce p rx t)) (p2 .index found (int 0))), .int⟩
  -- `A.Last[]` is the last element, `A.Last[N]` the one N before it (Book of
  -- Verse ch. 3): failing when there is none
  | "Last", [] => return ⟨.seq start (p2 .index (.local ta) (p2 .sub len (int 1))), t⟩
  | "Last", [n] =>
    let es ← elabInts ctx p [n]
    return ⟨.seq start (p2 .index (.local ta) (p2 .sub (p2 .sub len (int 1)) es[0]!)), t⟩
  | "RemoveElement", [i] =>
    let es ← elabInts ctx p [i]
    let tk ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tk)) (p2 .lt (.local tk) len)
    return ⟨.seq start (.seq (.assign tk es[0]!) (.seq chk
      (p2 .concat (← slice (int 0) (.local tk)) (← slice (p2 .add (.local tk) (int 1)) len)))), r.ty⟩
  | "ReplaceElement", [i, x] =>
    let es ← elabInts ctx p [i]
    let rx ← elabE ctx x (some t)
    return ⟨.seq start (.prim .arrSet [.local ta, es[0]!, ← coerce p rx t]), r.ty⟩
  | "Insert", [i, b] =>
    let es ← elabInts ctx p [i]
    let rb ← elabE ctx b (some r.ty)
    let tk ← fresh .int
    let tb ← fresh r.ty
    let chk := Expr.seq (p2 .le (int 0) (.local tk)) (p2 .le (.local tk) len)
    return ⟨.seq start (.seq (.assign tk es[0]!) (.seq (.assign tb (← coerce p rb r.ty)) (.seq chk
      (p2 .concat (p2 .concat (← slice (int 0) (.local tk)) (.local tb)) (← slice (.local tk) len))))), r.ty⟩
  -- (#150) the first occurrence of `x`, removed or replaced: failing when
  -- there is none
  | "RemoveFirstElement", [x] | "ReplaceFirstElement", [x, _] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t s!"the element type of {m}")
    let rx ← elabE ctx x (some t)
    let tx ← fresh t
    let ti ← fresh .int
    let found := Expr.forE ti (.prim .range [int 0, p2 .sub len (int 1)])
      (p2 .eq (p2 .index (.local ta) (.local ti)) (.local tx)) (.local ti)
    let tk ← fresh .int
    let first := Expr.seq (.assign tx (← coerce p rx t)) (.assign tk (p2 .index found (int 0)))
    match m, args with
    | "ReplaceFirstElement", [_, y] =>
      let ry ← elabE ctx y (some t)
      return ⟨.seq start (.seq first (.prim .arrSet [.local ta, .local tk, ← coerce p ry t])), r.ty⟩
    | _, _ =>
      return ⟨.seq start (.seq first
        (p2 .concat (← slice (int 0) (.local tk)) (← slice (p2 .add (.local tk) (int 1)) len))), r.ty⟩
  -- `A.Remove[i, j]`: without the elements i…j-1 (0 ≤ i ≤ j ≤ the length)
  | "Remove", [a, b] =>
    let es ← elabInts ctx p [a, b]
    let tlo ← fresh .int
    let thi ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tlo)) (.seq (p2 .le (.local tlo) (.local thi))
      (p2 .le (.local thi) len))
    return ⟨.seq start (.seq (.assign tlo es[0]!) (.seq (.assign thi es[1]!) (.seq chk
      (p2 .concat (← slice (int 0) (.local tlo)) (← slice (.local thi) len))))), r.ty⟩
  -- every occurrence of `x`, removed or replaced: never failing
  | "RemoveAllElements", [x] | "ReplaceAllElements", [x, _] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t s!"the element type of {m}")
    let rx ← elabE ctx x (some t)
    let tx ← fresh t
    let te ← fresh t
    let setX := Expr.assign tx (← coerce p rx t)
    match m, args with
    | "ReplaceAllElements", [_, y] =>
      let ry ← elabE ctx y (some t)
      let ty ← fresh t
      return ⟨.seq start (.seq setX (.seq (.assign ty (← coerce p ry t))
        (.forE te (.local ta) (.lit .void)
          (.ite (p2 .eq (.local te) (.local tx)) (.local ty) (.local te))))), r.ty⟩
    | _, _ =>
      return ⟨.seq start (.seq setX (.forE te (.local ta) (p2 .ne (.local te) (.local tx)) (.local te))), r.ty⟩
  -- `A.ReplaceAll(Pattern, Replacement)`: a helper written in Verse
  | "ReplaceAll", [pat, rep] =>
    if !t.comparable ctx.types then eerr p (notComparable ctx.types t "the element type of ReplaceAll")
    let nm := s!"$receiver{ta}"
    let c2 := { ctx with locals := { name := nm, slot := ta, ty := r.ty, mutable := false } :: ctx.locals }
    let rc ← elabApp c2 p (.ident p "$replaceAll") [.ident p nm, pat, rep] false (some r.ty)
    return ⟨.seq start rc.e, r.ty⟩
  | _, _ => eerr p s!"unknown array method '{m}' with {args.length} argument(s) (openverse supports Slice, Find, RemoveFirstElement, RemoveElement, Remove, RemoveAllElements, ReplaceFirstElement, ReplaceElement, ReplaceAllElements, ReplaceAll, Insert, Last)"

/-- `A[i]` on an array (failable) or `T(k)` on a tuple. -/
partial def elabIndexLike (ctx : Ctx) (p : Pos) (r : R) (args : List SExpr) (bracket : Bool) : EM R := do
  -- a call of a function value (#210): of its shape's method
  if let .struct n _ := r.ty then
    if let some (_, effs) := FnValues.parseName n then
      if effs.contains "decides" && !bracket then
        eerr p s!"a value of type {r.ty.show} can fail: call it with […]"
      if !effs.contains "decides" && bracket then
        eerr p s!"a value of type {r.ty.show} cannot fail: call it with (…)"
      if effs.contains "suspends" && !ctx.suspends then
        eerr p s!"a value of type {r.ty.show} suspends: it can only be called in a <suspends> function (#156)"
      -- (one tuple argument flattens into several parameters)
      let k := (FnValues.parseName n).elim 0 (·.1)
      if args.length != k && !(args.length == 1 && k > 1) then
        eerr p s!"a value of type {r.ty.show} takes {k} argument(s), found {args.length}"
      let t ← fresh r.ty
      let nm := s!"$fnval{t}"
      let ctx' := { ctx with locals := { name := nm, slot := t, ty := r.ty, mutable := false } :: ctx.locals }
      let rc ← elabApp ctx' p (.member p (.ident p nm) (FnValues.callOf n)) args bracket none
      return ⟨.seq (.assign t r.e) rc.e, rc.ty⟩
  match r.ty, args, bracket with
  | .arr t, [i], true =>
    let ri := widenR ctx.types (← elabE ctx i (some .int))
    if ri.ty != .int then eerr p s!"an array index must be an int, found {ri.ty.show}"
    return ⟨p2 .index r.e ri.e, t⟩
  | .map kt vt, [k], true =>
    let tm ← fresh r.ty
    let rk ← elabE ctx k (some kt)
    let tk ← fresh kt
    let tp ← fresh (.tup [kt, vt])
    return ⟨.seq (.assign tm r.e) (.seq (.assign tk (← coerce p rk kt)) (mapLookup tm tk tp)), vt⟩
  | .tup ts, [.int _ k], false =>
    if k < 0 || k.toNat ≥ ts.length then eerr p s!"tuple index {k} out of range"
    return ⟨.prim (.tupGet k.toNat) [r.e], ts[k.toNat]!⟩
  | t, _, _ => eerr p s!"cannot call or index a value of type {t.show}"

/-- Two types with an int in one where the other has a rational, at the
    same place inside them (#116). -/
partial def ratMismatch : Ty → Ty → Bool
  | .int, .rational | .rational, .int => true
  | .arr a, .arr b | .opt a, .opt b => ratMismatch a b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).any fun (a, b) => ratMismatch a b
  | .tup as, .arr b | .arr b, .tup as => as.any (ratMismatch · b)
  | .map k v, .map k' v' => ratMismatch k k' || ratMismatch v v'
  | .struct a as, .struct b bs => a == b && as.length == bs.length && (as.zip bs).any fun (x, y) => ratMismatch x y
  | _, _ => false

/-- Two different scalar types at the same place inside two types (#127):
    `1 = 1.0` or `array{1} = array{'a'}` would compare values Verse Core
    holds differently, always unequal. -/
partial def scalarMismatch : Ty → Ty → Bool
  | .arr a, .arr b | .opt a, .opt b => scalarMismatch a b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).any fun (a, b) => scalarMismatch a b
  | .tup as, .arr b | .arr b, .tup as => as.any (scalarMismatch · b)
  | .map k v, .map k' v' => scalarMismatch k k' || scalarMismatch v v'
  | .struct a as, .struct b bs => a == b && as.length == bs.length && (as.zip bs).any fun (x, y) => scalarMismatch x y
  | a, b =>
    let scalar : Ty → Bool := fun
      | .int | .logic | .char | .char32 | .rational | .float | .enum _ => true
      | _ => false
    scalar a && scalar b && !(a == b)

/-- A call of a rational helper (#116), `$ratMake` or `$ratLt`. -/
partial def ratCall (ctx : Ctx) (p : Pos) (f : String) (args : List Expr) : EM Expr := do
  let some s := ctx.sig? f | eerr p "internal error: the rational helpers are missing"
  return .call s.idx args

/-- The test of `x op y`, where one operand is a rational and the other an
    int or a rational (#116): it fails when the comparison does not hold.
    Rationals are in lowest terms, so `=` and `<>` are the tuples'; an
    ordering is `$ratLt`'s. -/
partial def ratTest (ctx : Ctx) (p : Pos) (op : String) (x y : R) : EM Expr := do
  let asRat (r : R) : EM Expr := match r.ty with
    | .rational => pure r.e
    | .int => pure (.prim .mkTup [r.e, .lit (.int 1)])
    | t => eerr p s!"'{op}' compares a rational with an int or a rational, not with {t.show}"
  let xa ← asRat x
  let ya ← asRat y
  match op with
  | "=" => return p2 .eq xa ya
  | "<>" => return p2 .ne xa ya
  | "<" => ratCall ctx p "$ratLt" [xa, ya]
  | ">" => ratCall ctx p "$ratLt" [ya, xa]
  | "<=" => return Expr.notE (← ratCall ctx p "$ratLt" [ya, xa])
  | _ => return Expr.notE (← ratCall ctx p "$ratLt" [xa, ya])

partial def elabCmp (ctx : Ctx) (p : Pos) (a : SExpr) (rest : List (String × SExpr)) : EM R := do
  let opOf : String → Prim
    | "=" => .eq | "<>" => .ne | "<" => .lt | "<=" => .le | ">" => .gt | _ => .ge
  -- (the orderings of floats are IEEE's, #127: false on NaN)
  let ordOf (op : String) (t : Ty) : Prim :=
    if t == .float then
      match op with
      | "<" => .flt | "<=" => .fle | ">" => .fgt | ">=" => .fge | _ => opOf op
    else opOf op
  let checkTys (op : String) (ta tb : Ty) : EM Unit := do
    if op == "=" || op == "<>" then
      if !isComparable ctx.types ta || !isComparable ctx.types tb then
        if !ta.comparable ctx.types then eerr p (notComparable ctx.types ta s!"an operand of '{op}'")
        if !tb.comparable ctx.types then eerr p (notComparable ctx.types tb s!"an operand of '{op}'")
        eerr p "these values cannot be compared"
      -- different types with the same Verse Core type (a char32 or an enum
      -- and an int, two structs with the same fields, also inside
      -- containers) would compare equal there
      -- (or could be, at some instance of the type parameters they mention:
      -- two different ones, or one and a type that several types share in
      -- Core, one with an int or a tuple)
      let (va, vb) := (ta.toVTy ctx.types, tb.toVTy ctx.types)
      let (pa, pb) := (!ta.params.isEmpty, !tb.params.isEmpty)
      if !(ta == tb) && ta != .never && tb != .never &&
          (va == vb || (pa && pb) || (pa && vb.shared) || (pb && va.shared)) then
        eerr p s!"'{op}' compares values of different types, {ta.show} and {tb.show}"
      -- (nor an int with a rational inside containers, #116: equal values
      -- that Verse Core holds differently, `1` and `(1, 1)`)
      if ratMismatch ta tb then
        eerr p s!"'{op}' compares values of different types, {ta.show} and {tb.show} (an int and a rational inside them: convert the ints first)"
      if scalarMismatch ta tb then
        eerr p s!"'{op}' compares values of different types, {ta.show} and {tb.show}"
    else if !((ta == .int && tb == .int) || (ta == .char && tb == .char) || (ta == .char32 && tb == .char32) ||
        (ta == .float && tb == .float)) then
      eerr p s!"'{op}' compares ints, chars, char32s or floats, found {ta.show} and {tb.show}"
  let ra := widenR ctx.types (← elabE ctx a none)
  -- (an array and a tuple compare as arrays: the tuple is converted)
  let asArr (r : R) (other : Ty) : EM R := do
    match r.ty, other with
    | .tup _, .arr _ => return ⟨← coerce p r other, other⟩
    | _, _ => return r
  match rest with
  | [(op, b)] =>
    let rb := widenR ctx.types (← elabE ctx b (some ra.ty))
    if ra.ty == .rational || rb.ty == .rational then
      let ta ← fresh ra.ty
      let tb ← fresh rb.ty
      let test ← ratTest ctx p op ⟨.local ta, ra.ty⟩ ⟨.local tb, rb.ty⟩
      return ⟨.seq (.assign ta ra.e) (.seq (.assign tb rb.e) (.seq test (.local ta))), ra.ty⟩
    let ra ← asArr ra rb.ty
    let rb ← asArr rb ra.ty
    checkTys op ra.ty rb.ty
    return ⟨p2 (ordOf op ra.ty) ra.e rb.e, ra.ty⟩
  | _ =>
    -- a chain: each operand is evaluated once, every adjacent pair is checked,
    -- and the result is the leftmost operand (Book of Verse §5.4)
    let t0 ← fresh ra.ty
    let mut prev := t0
    let mut prevTy := ra.ty
    let mut steps : Array Expr := #[.assign t0 ra.e]
    for (op, b) in rest do
      let rb := widenR ctx.types (← elabE ctx b (some prevTy))
      let rb ← asArr rb prevTy
      -- (the previous operand, as an array when this one is)
      let prevE ← match prevTy, rb.ty with
        | .tup _, .arr _ => coerce p ⟨.local prev, prevTy⟩ rb.ty
        | _, _ => pure (.local prev)
      let tb ← fresh rb.ty
      if prevTy == .rational || rb.ty == .rational then
        steps := steps.push (.assign tb rb.e)
        steps := steps.push (← ratTest ctx p op ⟨.local prev, prevTy⟩ ⟨.local tb, rb.ty⟩)
      else
        checkTys op (match prevTy, rb.ty with | .tup _, .arr _ => rb.ty | _, _ => prevTy) rb.ty
        steps := steps.push (.assign tb rb.e)
        steps := steps.push (p2 (ordOf op prevTy) prevE (.local tb))
      prev := tb
      prevTy := rb.ty
    return ⟨steps.foldr Expr.seq (.local t0), ra.ty⟩

/-- `elabSetWith`, given this block's functions (#325). -/
partial def elabSet (ctx : Ctx) (p : Pos) (lhs0 : SExpr) (op : Option String) (rhs0 : SExpr) : EM R :=
  elabSetWith elabE (fun c q r m => elabMember c q r m) ctx p lhs0 op rhs0

/-- `for` (#208, #314): `elabForWith`, given this block's functions (#325). -/
partial def elabFor (ctx : Ctx) (p : Pos) (clauses : List SExpr) (body : SExpr) (prepared : Bool := false)
    (firstDecides : Bool := false) (failure : Option SExpr := none) : EM R :=
  elabForWith elabAlts (fun c q i t pl => elabBranchAlts c q i t pl) elabE elabInts elabLoopGen elabSeq ctx p clauses body
    prepared firstDecides failure

/-- A condition's local types under its cast refinements. Its code is used
    only by the isolated branch-type probe. -/
partial def elabChoiceTypeCondition (ctx : Ctx) : List SExpr → EM (R × Ctx × Bool)
  | [] => pure (⟨.lit .void, .void⟩, ctx, false)
  | cl :: rest => do
    if let .decl p d none false (.app _ (.ident _ target) [x] true) := cl then
      let st ← get
      let rx ← elabE ctx x none
      let env := ctx.types
      if let some (source, _, targs, _, eqs, opened) := refiningCast? env target rx.ty (env.tvars.map (·.1)) then
        if env.isRefClass source && (opened.isEmpty || env.isRefClass target) then
          if let some (μ, opened) := castRefinement? env eqs opened (env.comparableArgs target targs) then
            let targs := targs.map fun t => t.subst (opened.filterMap fun (n, _, c) => if c then some (n, Ty.param n true) else none)
            let refine (t : Ty) := t.subst μ
            let ty := refine (.struct target targs)
            let slot ← fresh ty
            let c : Ctx := { ctx with
              locals := { name := d, slot, ty, mutable := false } :: (ctx.locals.map fun l => { l with ty := refine l.ty }),
              types := { env with tvars := (env.tvars.map (fun (n, t) => (n, refine t)) ++
                opened.map (fun (n, _, cmp) => (n, Ty.param n cmp))) } }
            let (r, c, _) ← elabChoiceTypeCondition c rest
            return (⟨.seq Expr.failV r.e, r.ty⟩, c, true)
      set st
    let (r, c) ← if Choice.hasChoice [cl] (choiceOrder ctx) then elabOneClauses ctx [cl]
      else elabSeq ctx [cl] none
    let (tail, c, refined) ← elabChoiceTypeCondition c rest
    return (⟨.seq r.e tail.e, tail.ty⟩, c, refined)

/-- An `if … else if … else …` with choices in its branches (#235): code that
    picks the branch, once, into a fresh slot (each condition a failure
    context of its own, tried when the ones before failed), and every
    branch's alternatives guarded by it (`B = j; a`), each seeing the names
    its conditions bind, at their written type or their join. -/
partial def elabBranchAlts (ctx : Ctx) (p : Pos) (i : SExpr) (sty : Option STy) (place : Option SExpr := none) :
    EM (Option Expr × Ty × List Expr × Bool) := do
  let i := pruneMethodCases ctx i
  let arms := Choice.arms i
  let bi ← fresh .int
  let mut conds : Array (Option Expr) := #[]
  let mut ctxs : Array Ctx := #[]
  let mut refined := false
  for (cs?, _) in arms do
    match cs? with
    | some cs =>
      let (rc, cT, refines) ← if ctx.typeOnly && choiceHasCast ctx i then
          elabChoiceTypeCondition { ctx with canFail := true, inTaking := true } cs
        else do
          let (rc, cT) ← if Choice.hasChoice cs (choiceOrder ctx) then elabOneClauses { ctx with canFail := true } cs
            else elabSeq { ctx with canFail := true, inTaking := true } cs none
          pure (rc, cT, false)
      refined := refined || refines
      if !(rc.e.mayFail ctx.sigProg) && (← get).fnNeeds.isEmpty && (← get).methodNeeds.isEmpty && !ctx.typeOnly then
        eerr p "the condition of this if cannot fail (Verse requires a failable condition)"
      conds := conds.push (some rc.e)
      ctxs := ctxs.push { cT with canFail := ctx.canFail, inTaking := ctx.inTaking }
    | none =>
      conds := conds.push none
      ctxs := ctxs.push ctx
  -- (from the last branch back: `if (c₀) then B := 0 else if (c₁) then B := 1 … else B := n`)
  let setB (j : Nat) : Expr := .assign bi (.lit (.int j))
  let pick := (conds.toList.zipIdx).foldr (fun (c?, j) acc => match c? with
    | some c => Expr.ite c (setB j) acc
    | none => setB j) (.lit .void)
  -- (the written type, or for `set L = if …` the type of `L`)
  let t? ← match ← sty.mapM (resolveTy ctx.types p) with
    | some t => pure (some t)
    | none => match place with
      | some l => tryCatch (do pure (some (← elabE ctx l none).ty)) fun _ => pure none
      | none => pure none
  -- (for the type only, #283: a value with a call with several values or a
  -- choice in it, which only a failure context that takes its values
  -- compiles, at the type of those values, as `option{…}` takes them)
  let elabA (c : Ctx) (a : SExpr) (t? : Option Ty) : EM R := do
    let wanted := t?
    let t? := if ctx.typeOnly then t?.map (·.subst c.types.tvars) else t?
    let r ← if ctx.typeOnly && Choice.hasLiftable a then do
      -- (a block's last value at the expected type, which `option{…}`
      -- does not pass into it, #383's review: `{ …; false }` against ?int;
      -- its `defer:`s after the value, as where it is lifted, #283, since
      -- the braces of `option{…}` hold clauses)
      let a := match a with
        | .block bp ss => SExpr.block bp (Choice.deferLast bp "$jdv" ss)
        | a => a
      let a := match a, t? with
        | .block bp ss@(_ :: _), some t =>
          SExpr.block bp (ss.dropLast ++ [.decl bp "$jv" (some t.toSTy) false (ss.getLast?.getD (.tuple bp [])), .ident bp "$jv"])
        | a, _ => a
      let r ← elabE c (.optionLit a.pos a) (t?.map .opt)
      match r.ty with
      | .opt t => pure ⟨r.e, t⟩
      | _ => pure r
    else elabE c a t?
    if ctx.typeOnly then
      if let some t := t? then discard <| coerce a.pos r t
    -- Report the original scope's bounds to the outer consumer. The arm's
    -- local comparable evidence must not constrain an unrefined else path.
    let bounds := Ty.mergeParamBounds ((ctx.types.tvars.map (·.2) ++ ctx.locals.map (·.ty)).flatMap Ty.paramsC)
    return { r with ty := if ctx.typeOnly then (wanted.getD r.ty).withParamBounds bounds else r.ty }
  let all : List (Nat × SExpr) := arms.zipIdx.flatMap fun ((_, arm), j) => ((Choice.alts? arm).getD [arm]).map (j, ·)
  -- (#366, the state before the alternatives, for the retries below)
  let st0 ← get
  let mut rs : Array (Nat × SExpr × R) := #[]
  for ((_, arm), j) in arms.zipIdx do
    let c := ctxs.getD j ctx
    for a in (Choice.alts? arm).getD [arm] do
      -- (without a type, each later one against the first's, else on its
      -- own, as `elabAlts` does, #32)
      let r ← match t?, rs[0]? with
        | some t, _ => elabA c a (some t)
        | none, none => do
          -- (#366) when the first needs another's type (`array{}` first):
          -- the first later one with a type on its own gives it; else the
          -- first one's own error, as before
          match ← tryCatch (do pure (Except.ok (← elabA c a none))) (fun e => pure (Except.error e)) with
          | .ok r => pure r
          | .error err =>
            if ctx.retries ≥ 3 then throw err
            let st ← get
            let mut ref? : Option Ty := none
            for (j', a') in all.drop 1 do
              if ref?.isSome then continue
              if let some r' ← tryCatch (do pure (some (← elabA { (ctxs.getD j' ctx) with retries := ctx.retries + 1 } a' none))) (fun _ => pure none) then
                ref? := some r'.ty
            set st
            match ref? with
            | some rt => elabA { c with retries := ctx.retries + 1 } a (some rt)
            | none => throw err
        | none, some (_, _, r0) =>
          if c.retries ≥ 3 then tryCatch (elabA c a none) fun _ => elabA c a (some r0.ty)
          else
            let c2 := { c with retries := c.retries + 1 }
            tryCatch (elabA c2 a (some r0.ty)) fun _ => elabA c2 a none
      rs := rs.push (j, a, r)
  let some (_, _, r0) := rs[0]? | eerr p "internal: an if without branches"
  let mut ty ← match t? with
    | some t => pure t
    | none => rs.toList.foldlM (fun acc (_, _, r) => join p acc r.ty none) r0.ty
  if ty == .never then eerr p "cannot infer the type of this if's choices"
  -- (#366) with nothing in common, every alternative against a later
  -- one's type instead, the first that fits them all, as `elabAlts` does
  if t?.isNone && ty == .any && ctx.retries < 3 then
    let env := (← get).env
    let mut found := false
    let stAfter ← get
    for (_, _, r) in rs.toList.drop 1 do
      if found || r.ty == .any || r.ty == .never then continue
      -- (from the state before the alternatives: the first try's code and
      -- slots are not kept)
      set st0
      let attempt : EM (Array (Nat × SExpr × R)) := rs.mapM fun (j, a, _) => do
        let c := ctxs.getD j ctx
        return (j, a, ← elabA { c with retries := ctx.retries + 1 } a (some r.ty))
      match ← tryCatch (do pure (some (← attempt))) (fun _ => pure none) with
      | some rs' =>
        match rs'.toList.foldl (fun acc (_, _, r') => acc.bind fun t => joinTy env t r'.ty none) (some r.ty) with
        | some ty' =>
          if ty' != .any then
            ty := ty'; rs := rs'; found := true
          else set stAfter
        | none => set stAfter
      | none => set stAfter
  let es ← rs.toList.mapM fun (j, a, r) => do
    return Expr.seq (.prim .eq [.local bi, .lit (.int j)]) (← coerce a.pos r ty)
  return (some pick, ty, es, refined)

/-- The alternatives of a choice (#208), at its written type or at their
    join (each one against the first's type, else on its own, as `if`'s
    branches are), and that type. -/
partial def elabAlts (ctx : Ctx) (p : Pos) (b : Choice.Binding) : EM (Ty × List Expr) := do
  -- (a choice or a call with several values left in an alternative is in a
  -- failure context that takes values, where it cannot be lifted from)
  let ctx := { ctx with inTaking := true }
  let alts := b.alts
  -- (the written type, or for `set L = a | b` the type of `L`)
  let t? ← match ← b.ty.mapM (resolveTy ctx.types p) with
    | some t => pure (some t)
    | none => match b.place with
      | some l => tryCatch (do pure (some (← elabE ctx l none).ty)) fun _ => pure none
      | none => pure none
  match t? with
  | some t => return (t, ← alts.mapM fun a => do coerce a.pos (← elabE ctx a (some t)) t)
  | none =>
    let some a0 := alts.head? | eerr p "internal: a choice without alternatives"
    -- (#366) a first alternative that needs another's type (`array{} | …`):
    -- a later one on its own, then all against its type; when none fits,
    -- the first one's own error, as before
    let st0 ← get
    let r0? ← tryCatch (do pure (Except.ok (← elabE ctx a0 none))) fun e => pure (Except.error e)
    let r0 ← match r0? with
      | .ok r => pure r
      | .error err =>
        if ctx.retries ≥ 3 then throw err
        let c2 := { ctx with retries := ctx.retries + 1 }
        for a in alts.tail do
          let res ← tryCatch (do
              let ra ← elabE c2 a none
              let rs' ← alts.mapM fun a' => elabE c2 a' (some ra.ty)
              let ty ← rs'.foldlM (fun acc r => join p acc r.ty none) ra.ty
              pure (some (ty, ← ((alts.zip rs').mapM fun (a', r) => coerce a'.pos r ty)))) fun _ => pure none
          if let some out := res then return out
        throw err
    -- (each later one against the first's type, else on its own, to join;
    -- a few levels deep, then on its own first, as the join needs, #32)
    let rs ← alts.tail.mapM fun a =>
      if ctx.retries ≥ 3 then tryCatch (elabE ctx a none) fun _ => elabE ctx a (some r0.ty)
      else
        let c2 := { ctx with retries := ctx.retries + 1 }
        tryCatch (elabE c2 a (some r0.ty)) fun _ => elabE c2 a none
    let ty ← rs.foldlM (fun acc r => join p acc r.ty none) r0.ty
    if ty == .never then eerr p "cannot infer the type of this choice"
    -- (#366) with nothing in common, every alternative against a later
    -- one's type instead, the first that fits them all: `false | option{4}`
    -- is a `?int`, as `option{4} | false` is; else `any`, as before
    if ty == .any && ctx.retries < 3 then
      let env := (← get).env
      let stAfter ← get
      for r in rs do
        if r.ty == .any || r.ty == .never then continue
        -- (from the state before the alternatives: the first try's code and
        -- slots are not kept)
        set st0
        let c2 := { ctx with retries := ctx.retries + 1 }
        match ← tryCatch (do pure (some (← alts.mapM fun a => elabE c2 a (some r.ty)))) (fun _ => pure none) with
        | some rs' =>
          match rs'.foldl (fun acc r' => acc.bind fun t => joinTy env t r'.ty none) (some r.ty) with
          | some ty' =>
            if ty' != .any then
              return (ty', ← ((alts.zip rs').mapM fun (a, r') => coerce a.pos r' ty'))
            set stAfter
          | none => set stAfter
        | none => set stAfter
    return (ty, ← ((alts.zip (r0 :: rs)).mapM fun (a, r) => coerce a.pos r ty))

/-- The clauses of a failure context that takes its first success (an `if`
    condition, `first{…}`), when one of them binds a choice (#208):
    `Expr.firstE` over the clauses, each choice an `Expr.chooseFirst` around
    the clauses after it, which `break` when all of them succeed. Its value is
    `void`: an `if` and `first{…}` read their clauses' values through names. -/
partial def elabOneClauses (ctx : Ctx) (cs : List SExpr) : EM (R × Ctx) := do
  let ctx := { ctx with liftWhy := "" }
  -- (a `break` here would leave `firstE`'s loop, not the program's)
  let (code, ctx') ← elabOneGo { ctx with inLoop := false, inChoice := ctx.inLoop, inTaking := true }
    (Choice.prepare cs (choiceValues ctx) (choiceField ctx) (fieldOrder := choiceOrder ctx)
      (keepBranches := choiceHasCast ctx))
  return (⟨Expr.firstE code, .void⟩, { ctx' with inLoop := ctx.inLoop, inChoice := ctx.inChoice, inTaking := ctx.inTaking })

partial def elabOneGo (ctx : Ctx) : List SExpr → EM (Expr × Ctx)
  | [] => return (Expr.brkV, ctx)
  | cl :: rest => do
    if let .app p (.ident _ "$defer") _ _ := cl then
      eerr p "defer: cannot be a clause of an if condition or first{…} that has a choice (#208)"
    -- (#283) the choice of an `if`'s branches, each guarded by its branch
    -- (`Choice.prepare`), with no type written: at the branches' join, as
    -- the `if`'s value has, found by elaborating the `if` apart for the type
    -- only, `$joinOf` (for `set L = if …`, at `L`'s type)
    let cl ← match cl with
      | .decl p x none false (.app q f@(.ident _ "$choice") as false) =>
        match as.findSome? (fun | .app _ (.ident _ "$joinOf") (i :: l) false => some (i, l.head?) | _ => none) with
        | some (i, place) =>
          let st ← get
          let (_, ty, _, _) ← elabBranchAlts { ctx with canFail := true, inTaking := true, typeOnly := true } p i none place
          restoreConstructProbe ctx st
          pure (.decl p x (some ty.toSTy) false
            (.app q f (as.filter fun | .app _ (.ident _ "$joinOf") _ _ => false | _ => true) false))
        | none => pure cl
      | cl => pure cl
    let cl := pruneMethodBinding ctx cl
    if let some b@{ branchy := some i, .. } := Choice.binding? cl then
      if choiceHasCast ctx i then
        let p := b.pos
        let t := s!"$refineChoice{p.line}_{p.col}{b.name}"
        -- Infer the element type before putting the remaining clauses in
        -- the branch. Each option takes the branch's first value for types.
        let st ← get
        let (_, ty, _, refined) ← elabBranchAlts { ctx with typeOnly := true } p i b.ty b.place
        restoreConstructProbe ctx st
        if !refined then
          if Choice.plainBranches Choice.hasLiftable i then
            return ← elabOneChoice ctx b rest
          return ← elabOneGo ctx (Choice.prepare [cl] (choiceValues ctx) (choiceField ctx)
            (site := b.name) (fieldOrder := choiceOrder ctx) ++ rest)
        if ctx.typeOnly then
          checkNewLocal ctx p b.name
          let slot ← fresh ty
          return ← elabOneGo { ctx with locals := { name := b.name, slot, ty, mutable := false } :: ctx.locals } rest
        let key := contKey ctx p b.name (i :: rest) ++ firstReturnKey ctx rest
        let request := ctx.types.loopRequests.find? (·.key == key)
        let hasLater := rest.any fun cl => match Choice.binding? cl with
          | some { branchy := some next, .. } => choiceHasCast ctx next
          | some { alts, .. } => alts.any Choice.hasLiftable
          | none => false
        if request.isNone && hasLater then
          let st0 ← get
          let slot ← fresh ty
          let c := { ctx with locals := { name := b.name, slot, ty, mutable := false } :: ctx.locals }
          let (code, c2) ← elabOneGo c rest
          let fx := (← get).fx
          match contLiftOf ctx c2 p b.name [i] rest fx with
          | .ok lift =>
            modify fun s => { s with loopFirst := s.loopFirst ++
              [{ g := "", pos := p, itemCode := .lit .void, argSet := none, lift := .ok lift }] }
            return (code, c2)
          | .error _ => set st0
        let request := request.filter fun l =>
          ctx.acceptsHelper l
        let binds := (b.name :: Choice.boundIn rest).eraseDups
        let vars := rest.filterMap fun | .decl _ n _ true _ => some n | _ => none
        let tup := SExpr.tuple p (binds.map (SExpr.ident p ·) ++ [.ident p "true"])
        let consume (arm : SExpr) : SExpr :=
          let clauses := Choice.prepare [.decl p b.name (some ty.toSTy) false arm]
            (choiceValues ctx) (choiceField ctx) (site := t) (fieldOrder := choiceOrder ctx)
            (keepBranches := choiceHasCast ctx)
          let tail := match request with
            | some l =>
              -- The continuation is part of the search, before firstP
              -- commits this value. Failure must retry the next alternative.
              let result := t ++ "$continuation"
              [.decl p result none false (.app p (.ident p l.name) l.args true), .ident p result]
            | none => rest ++ [tup]
          .optionLit p (.app p (.ident p "$firstP") [.block p (clauses ++ tail)] false)
        let selected := Choice.consumeBranches i t consume
        -- A selected branch with no successful value gives none. Query it
        -- after selection so an alternative's failure cannot select else.
        let get (j : Nat) := SExpr.app p (.ident p t) [.int p (j : Int)] false
        let unpack := binds.zipIdx.map fun (n, j) => SExpr.decl p n none (vars.contains n) (get j)
        let writes := request.toList.flatMap fun l => l.sets.zipIdx.map fun (n, j) =>
          SExpr.set p (.ident p n) none (get (l.binds.length + j))
        let unpack := match request with
          | some l => firstUnpack p l t
          | none => unpack ++ writes
        let (code, c) ← elabOneGo ctx ([.decl p t none false (.query p selected)] ++ unpack)
        return (code, { c with inlineScopes := Choice.inlineScopesAfter ctx.inlineScopes rest })
    match Choice.binding? cl with
    | some b@{ each := some (.app _ (.ident _ "$loop") lp false), .. } =>
      -- (one taken lazily, #246: a loop over its values, each followed by
      -- the clauses after it, which leave the loop when they succeed; the
      -- code after the loop says whether one did)
      let p := b.pos
      let g := match lp with | .ident _ g :: _ => g | _ => ""
      -- (when what it runs once for all the values of an item has effects,
      -- asked for by an earlier elaboration: a call of a function of its
      -- own that runs the clauses after it too, then the names they bind)
      if let some l := (if ctx.typeOnly then none else ctx.types.loopRequests.find? (·.key == firstKey ctx p lp b.name b.ty rest)) then
        let t := s!"$ft{p.line}_{p.col}"
        let (code, c) ← elabOneGo ctx ([.decl p t none false (.app p (.ident p l.name) l.args true)] ++
          firstUnpack p l t)
        return (code, { c with inlineScopes := Choice.inlineScopesAfter ctx.inlineScopes rest })
      let fx0 := (← get).fx
      modify fun st => { st with fx := [] }
      let lg ← elabLoopGen ctx p lp
      let ty ← match ← b.ty.mapM (resolveTy ctx.types p) with
        | some t => pure t
        | none => pure lg.vty
      checkNewLocal ctx p b.name
      let x ← fresh ty
      let c1 := { ctx with locals := { name := b.name, slot := x, ty, mutable := false } :: ctx.locals }
      let (inner, c2) ← elabOneGo c1 rest
      let fxB := (← get).fx
      modify fun st => { st with fx := fx0 }
      for (k, q, via) in fxB do noteFx q [k] via
      let isS (f : Nat) : Bool := ctx.sigs.any fun s => s.idx == f && s.suspends
      -- (the values at the function's result type, at the type arguments
      -- this call gives, for a generic one)
      let lift := firstLiftOf ctx c2 p g lp b.name b.ty rest fxB (ctx.suspends && Suspend.hasSusp isS inner) lg.vty lg.instances
      modify fun st => { st with loopFirst := st.loopFirst ++
        [{ g, pos := p, itemCode := lg.itemCode, argSet := lg.argSet, lift }] }
      let bindX ← coerce p ⟨lg.value, lg.vty⟩ ty
      let done ← fresh .logic
      let vd : Expr := .lit .void
      let body : Expr := .seq
        (.ite (p2 .eq (.local lg.sp) (.lit (.int 0))) (.seq (.assign done (.lit (.logic true))) Expr.brkV) vd)
        (.seq lg.step (.ite (.prim .query [.local lg.has])
          (.seq (.ite (.seq (.assign x bindX) (.seq inner Expr.failV)) vd vd) lg.after) vd))
      return (.seq lg.init (.seq (.assign done (.lit (.logic false))) (.seq (.loop body)
        (.ite (p2 .eq (.local done) (.lit (.logic false))) Expr.brkV vd))), c2)
    | some b@{ each := some arr, .. } =>
      -- (a call of a recursive function with several values, #235: each
      -- element of the array of its values in turn, the clauses after it
      -- in the filter, as `chooseFirst` does with alternatives)
      let p := b.pos
      let ra ← elabE ctx arr none
      let ety ← match ra.ty with
        | .arr t => pure t
        | t => eerr p s!"internal: the values of a call are {t.show}"
      let ty ← match ← b.ty.mapM (resolveTy ctx.types p) with
        | some t => pure t
        | none => pure ety
      checkNewLocal ctx p b.name
      let e ← fresh ety
      let x ← fresh ty
      let c1 := { ctx with locals := { name := b.name, slot := x, ty, mutable := false } :: ctx.locals }
      let (inner, c2) ← elabOneGo c1 rest
      let bindX ← coerce p ⟨.local e, ety⟩ ty
      return (.forE e ra.e (.seq (.assign x bindX) (.seq inner Expr.failV)) (.lit .void), c2)
    | some b@{ place := none, branchy := none, each := none, .. } =>
      if b.alts.any Choice.hasLiftable then
        -- (a choice whose alternatives have several values themselves, or
        -- clauses to lift, #283: each alternative with the clauses after
        -- it, in a first{…} of its own, so that its values are taken in
        -- order and the clauses run for each; the first success gives the
        -- names they bind, in a tuple)
        let p := b.pos
        let finish (action : EM (Expr × Ctx)) : EM (Expr × Ctx) := do
          let (code, c) ← action
          return (code, { c with inlineScopes := Choice.inlineScopesAfter ctx.inlineScopes rest })
        -- (with the binding's name: an inlined body's position is every
        -- site's, #314)
        let t := s!"$ct{p.line}_{p.col}{b.name}"
        let binds := (b.name :: Choice.boundIn rest).eraseDups
        let vars := rest.filterMap fun | .decl _ n _ true _ => some n | _ => none
        let tup : SExpr := .tuple p (binds.map (SExpr.ident p ·) ++ [.ident p "true"])
        let liftAlt (a : SExpr) (i : Nat) : List SExpr :=
          Choice.prepare [.decl p b.name b.ty false a] (choiceValues ctx) (choiceField ctx)
            (fieldOrder := choiceOrder ctx)
            (site := s!"{t}a{i}") (keepBranches := choiceHasCast ctx)
        let alt (a : SExpr) (i : Nat) : SExpr :=
          .app p (.ident p "$firstP") [.block p (liftAlt a i ++ rest ++ [tup])] false
        let copied : List SExpr := [.decl p t none false (Choice.mk p (b.alts.zipIdx.map fun (a, i) => alt a i))] ++
          binds.zipIdx.map fun (n, i) => .decl p n none (vars.contains n) (.app p (.ident p t) [.int p (i : Int)] false)
        -- (#335: another such choice in the clauses after it: those clauses a
        -- function of their own, which each alternative calls, instead of a
        -- copy in each, which doubled the code with each such choice)
        let isComposed (c : SExpr) : Bool := match Choice.binding? c with
          | some { place := none, branchy := none, each := none, alts := as, .. } => as.any Choice.hasLiftable
          -- A later typed dispatch stays a branch binding until its
          -- receiver prefix is elaborated. Its lifted arms would copy
          -- this same suffix once prepared, just as composed alternatives do.
          | some { branchy := some i, .. } => !Choice.plainBranches Choice.hasLiftable i
          | _ => false
        if rest.any isComposed then
          let req := if ctx.typeOnly then none else ctx.types.loopRequests.find? (·.key == contKey ctx p b.name (b.alts ++ rest) ++ firstReturnKey ctx rest)
          -- (asked for where more effects are allowed than here, as in a
          -- function of its own of a call taken lazily, #246: copied)
          let fits (l : Choice.FirstLift) : Bool :=
            ctx.acceptsHelper l
          if let some l := req then
            if !fits l then return ← finish (elabOneGo ctx copied)
            -- (the call a clause, whose failure goes back into the
            -- alternative's own choices, then its tuple the value)
            let kt := s!"{t}k"
            let altK (a : SExpr) (i : Nat) : SExpr :=
              .app p (.ident p "$firstP") [.block p (liftAlt a i ++
                [.decl p kt none false (.app p (.ident p l.name) l.args true), .ident p kt])] false
            return ← finish (elabOneGo ctx ([.decl p t none false (Choice.mk p (b.alts.zipIdx.map fun (a, i) => altK a i))] ++
              firstUnpack p l t))
          -- (the first elaboration: one alternative with the clauses after it,
          -- for their names' types and effects, and the function asked for;
          -- its code is not kept, as the next elaboration has the function)
          if let some a0 := b.alts.head? then
            let st0 ← get
            let fx0 := st0.fx
            modify fun st => { st with fx := [] }
            -- (each other alternative alone, without the clauses after it: its
            -- value's type, which must be the first's, as the function takes
            -- one; and the continuations in it, asked for in this elaboration
            -- too, so that nesting takes no more elaborations)
            let mut tys : List Ty := []
            for (a, i) in b.alts.zipIdx do
              let r ← elabE { ctx with canFail := true, inTaking := true }
                (.app p (.ident p "$firstP") [.block p (liftAlt a i ++ [.ident p b.name])] false) none
              tys := tys ++ [r.ty]
            let same := tys.all (some · == tys.head?)
            -- (what refuses it known before the trial, which then costs nothing)
            let ok := same
            let (code1, c1) ← if ok then elabOneGo ctx ([.decl p t none false (alt a0 0)] ++
                binds.zipIdx.map fun (n, i) => .decl p n none (vars.contains n) (.app p (.ident p t) [.int p (i : Int)] false))
              else pure (Expr.lit .void, ctx)
            let fxB := (← get).fx
            match (if ok then contLiftOf ctx c1 p b.name b.alts rest fxB else .error "alternatives of different types") with
            | .ok lift =>
              let use : LoopUse := { g := "", pos := p, itemCode := .lit .void, argSet := none, lift := .ok lift }
              modify fun st => { st with fx := fx0 }
              modify fun st => { st with loopFirst := st.loopFirst ++ [use] }
              for (k, q, via) in fxB do noteFx q [k] via
              return ← finish (pure (code1, c1))
            | .error _ => set st0
        return ← finish (elabOneGo ctx copied)
      let p := b.pos
      let n := b.name
      let (ty, es) ← elabAlts ctx p b
      checkNewLocal ctx p n
      let k ← fresh .int
      let x ← fresh ty
      let c1 := { ctx with locals := { name := n, slot := x, ty, mutable := false } :: ctx.locals }
      let (inner, c2) ← elabOneGo c1 rest
      return (Expr.chooseFirst k x es inner, c2)
    | some b =>
      elabOneChoice ctx b rest
    | none =>
      let (r, c1) ← elabStmt ctx cl none
      let (inner, c2) ← elabOneGo c1 rest
      return (.seq r.e inner, c2)

partial def elabOneChoice (ctx : Ctx) (b : Choice.Binding) (rest : List SExpr) : EM (Expr × Ctx) := do
  let p := b.pos
  let n := b.name
  let (pre, ty, es, _) ← match b.branchy with
    | some i => elabBranchAlts ctx p i b.ty b.place
    | none => do let (ty, es) ← elabAlts ctx p b; pure (none, ty, es, false)
  checkNewLocal ctx p n
  let k ← fresh .int
  let x ← fresh ty
  let c1 := { ctx with locals := { name := n, slot := x, ty, mutable := false } :: ctx.locals }
  let (inner, c2) ← elabOneGo c1 rest
  let code := Expr.chooseFirst k x es inner
  return ((pre.map (Expr.seq · code)).getD code, c2)

/-- A call of a recursive function with several values that its consumer
    takes lazily (#246), `$loop(F, params, clauses, r := tail)`, its
    parameters bound by the consumer's clauses before it, to its
    arguments. It runs as a loop over a stack of items, each `(k, F's
    parameters and the names its clauses and conditions bind)`: the
    alternative to run, or -1 to run the clauses and pick the branch of its
    last `if` first (when the clauses fail, the call has no values; what its
    arguments did stays, as for a call computed eagerly). A step pops one
    and runs one alternative. A value is the step's, for the consumer to
    compute; a call of `F` evaluates its arguments and pushes the item that
    starts it. The item that resumes at the next alternative of the choice,
    if any, is pushed below that one (with the names as the arguments left
    them), or once the consumer took or rejected the value (as the consumer
    left them): so the values come in the Verse Calculus's order, depth
    first. The stack is a list of cells (`$lazycell`), so a step costs the
    same however deep the stack is. -/
partial def elabLoopGen (ctx : Ctx) (p : Pos) (lp : List SExpr) : EM LoopGen := do
  let [.ident _ g, .block _ ps, .block _ cls, .decl _ _ (some rsty) _ tail] := lp
    | eerr p "internal: a $loop marker (#246)"
  -- (a strongly connected group's, #283)
  if let .app _ (.ident _ "$group") (tail0 :: members) false := tail then
    let names := g :: members.filterMap fun
      | .app _ (.ident _ "$member") (.ident _ h :: _) false => some h
      | _ => none
    let generic := names.any fun h => ((ctx.sig? h).map (!·.tparams.isEmpty)).getD false
    let pure := names.all fun h => ((ctx.sig? h).map (·.fx.isEmpty)).getD false
    if !generic || !pure then
      return ← elabLoopGenGroupWith elabE elabSeq ctx p g ps cls rsty tail0 members
    return ← tryCatch (elabLoopGenGroupWith elabE elabSeq ctx p g ps cls rsty tail0 members) fun _ => do
      -- Polymorphic recursion was already accepted through F$all. Restart
      -- choice lowering for this group, with all eager restrictions intact.
      modify fun st => { st with eagerNeeds := g :: st.eagerNeeds }
      let sp ← fresh .int
      let has ← fresh .logic
      return { init := .lit .void, step := .lit .void, sp, has, value := .prim .fail [],
               after := .lit .void, vty := ← resolveTy ctx.types p rsty, itemCode := .lit .void, argSet := none }
  let vd : Expr := .lit .void
  -- (the parameters, bound by the consumer's clauses: the loop has slots
  -- of its own for them, so that the call, run again by a loop of its
  -- consumer's, starts from its arguments, not from what its last run left)
  let args ← ps.mapM fun
    | .ident q n => match ctx.lookup n with
      | some l => pure l
      | none => eerr q s!"internal: parameter {n} of a $loop (#246)"
    | e => eerr e.pos "internal: a $loop parameter (#246)"
  let pls ← args.mapM fun l => do return { l with slot := ← fresh l.ty }
  -- (the result type: the signature's, at the type arguments the
  -- arguments give, for a generic one, #235)
  let rty ← match ctx.sig? g with
    | some sig =>
      if sig.tparams.isEmpty then resolveTy ctx.types p rsty else
      match (sig.params.zip args).foldlM (fun σ (pt, l) => Ty.matchArg ctx.types σ pt l.ty) [] with
      | some σ =>
        if let some (v, _) := sig.tparams.find? fun (v, _) => (σ.lookup v).isNone then
          eerr p s!"{g}'s type parameter {v} is not determined by its arguments' types here (#235)"
        pure (sig.ret.subst σ)
      | none => eerr p s!"internal: the arguments of {g} (#235)"
    | none => resolveTy ctx.types p rsty
  let lctx : Ctx := { ctx with locals := pls.reverse ++ ctx.locals }
  let newOf (c : Ctx) : List Local := c.locals.take (c.locals.length - lctx.locals.length)
  -- (the clauses, then each branch's conditions)
  let (rc, cc) ← elabSeq { lctx with canFail := true, inTaking := true } cls none
  let k ← fresh .int
  let code ← elabLoopTailWith elabSeq cc tail k 0
  let armCode := code.arms
  -- (every name to save in an item: the parameters, then the others)
  let mut tls : List Local := pls
  for l in (newOf cc ++ armCode.toList.flatMap fun (ca, _) => newOf ca).reverse do
    if !tls.any (·.slot == l.slot) then tls := tls ++ [l]
  let tupTy : Ty := .tup (.int :: tls.map (·.ty))
  let cellTy : Ty := .struct "$lazycell" [tupTy]
  let cfs := ctx.types.fields "$lazycell" [tupTy]
  let (some (itemF, _), some (nextF, _)) := (fieldIndex cfs "$LItem", fieldIndex cfs "$LNext")
    | eerr p "internal: the stack cells of a $loop (#246)"
  let w ← fresh (.opt cellTy)
  let cell ← fresh cellTy
  let sp ← fresh .int
  let it ← fresh tupTy
  let has ← fresh .logic
  let nx ← fresh .int
  let item (kE : Expr) (vals : List Expr) : Expr := .prim .mkTup (kE :: vals)
  let cur : List Expr := tls.map (Expr.local ·.slot)
  let push (e : Expr) : Expr :=
    .seq (.assign cell (.heap (.new (ctx.types.tagOf "$lazycell")) [e, .local w]))
      (.seq (.assign w (.prim .mkSome [.local cell]))
        (.seq (.assign sp (p2 .add (.local sp) (.lit (.int 1)))) vd))
  -- (the branch an item takes: the first alternative of it)
  let total := code.next
  let starts : List Nat := (armCode.toList.foldl (fun (acc, n) (_, as) => (acc ++ [n], n + as.length)) ([], 0)).1
  let select := code.select
  -- (each alternative's code, numbered across the branches)
  let mut alts : Array Expr := #[]
  let mut values : Array (Nat × Expr) := #[]
  let mut itemCode : Expr := .seq rc.e code.itemCode
  let mut argSet : Option Pos := none
  for ((ca, as), start) in armCode.toList.zip starts do
    for (a, j) in as.zipIdx do
      let i := start + j
      let actx : Ctx := { ca with canFail := true, inTaking := true }
      let next? : Option Nat := if j + 1 < as.length then some (i + 1) else none
      let cont : Expr := match next? with
        | some n => push (item (.lit (.int (n : Nat))) cur)
        | none => vd
      match a with
      | .app q (.ident _ "$rec") args' false =>
        if argSet.isNone then
          argSet := args'.findSome? fun a' =>
            if Choice.anyE (fun | .set .. => true | _ => false) a' then some a'.pos else none
        let ts ← pls.mapM fun l => fresh l.ty
        let assigns ← elabLoopArgsWith elabE actx q g args' pls ts
        itemCode := .seq itemCode assigns
        -- (the item that resumes after the call, with the names as its
        -- arguments left them, below the one that starts it; when an
        -- argument fails, only the first)
        let start := item (.lit (.int (-1))) (ts.map Expr.local ++ cur.drop pls.length)
        alts := alts.push (.ite assigns (.seq cont (push start)) cont)
      | _ =>
        let r ← elabE actx a (some rty)
        values := values.push (i, ← coerce a.pos r rty)
        let nextK : Int := match next? with | some n => (n : Int) | none => -1
        alts := alts.push (.seq (.assign nx (.lit (.int nextK))) (.seq (.assign has (.lit (.logic true))) vd))
  let dispatch : Expr := (alts.toList.zipIdx).foldr (fun (a, i) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) a acc) vd
  let unpack : Expr := (tls.zipIdx).foldr (fun (l, j) acc =>
    .seq (.assign l.slot (.prim (.tupGet (j + 1)) [.local it])) acc) vd
  -- (the call's item: its parameters from the consumer's slots, its
  -- other names as they are)
  let init : Expr := .seq (.assign w (.lit .none)) (.seq (.assign sp (.lit (.int 0)))
    (push (item (.lit (.int (-1))) (args.map (Expr.local ·.slot) ++ cur.drop pls.length))))
  let step : Expr := Expr.seq (.assign sp (p2 .sub (.local sp) (.lit (.int 1))))
    (.seq (.ite (.assign cell (.prim .query [.local w]))
        (.seq (.assign it (.heap (.get itemF) [.local cell])) (.seq (.assign w (.heap (.get nextF) [.local cell])) vd)) vd)
    (.seq (.assign k (.prim (.tupGet 0) [.local it]))
    (.seq unpack
    (.seq (.assign has (.lit (.logic false)))
    (.seq (.ite (p2 .eq (.local k) (.lit (.int (-1))))
        (.ite (.seq rc.e select) vd (.seq (.assign k (.lit (.int (total : Nat)))) vd)) vd)
      dispatch)))))
  -- (the value of the alternative the step came to, which it left in `k`)
  let value : Expr := values.toList.foldr (fun (i, e) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) e acc) (.prim .fail [])
  let after : Expr := .ite (p2 .ge (.local nx) (.lit (.int 0))) (push (item (.local nx) cur)) vd
  return { init, step, sp, has, value, after, vty := rty, itemCode, argSet }

/-- Bind a selected spawn's defaults in the caller, then spawn an adapter
    whose result is the static declaration's result (task types are invariant). -/
partial def elabSpawnBound (ctx : Ctx) (p : Pos) (fname adapter : String)
    (args : List SExpr) : EM R := do
  let some s := ctx.sig? fname | eerr p s!"internal: no spawn signature for {fname}"
  let .struct "task" [ret] := ctx.retTy | eerr p "internal: no spawn factory result"
  let before := (← get).pendingSuspendingCasts
  let packed ← elabGenericCallWith elabE { ctx with suspends := true } p s args none (packArgs := true)
  let isS (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.suspends
  let skip (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.name == "$spawnMark"
  if before != (← get).pendingSuspendingCasts ||
      Suspend.countSusp isS (fun _ => false) false skip packed.e > 0 then
    eerr p "the arguments of a spawned call cannot suspend (#156)"
  noteFx p s.fx (some fname)
  let .tup ts := packed.ty | eerr p "internal: no packed spawn arguments"
  let receiver ← elabE ctx args[0]! none
  let .struct cls _ := receiver.ty | eerr p "internal: no concrete spawn receiver"
  let params := receiver.ty :: ts.drop 1
  let tps := Ty.mergeParamBounds ((ret :: params).flatMap Ty.paramsC)
  let selfTps := ((ctx.types.sparams.lookup cls).getD []).map (·.1)
  let adapter := s!"{adapter}_{(reprStr params ++ reprStr ret).hash}"
  if (ctx.sig? adapter).isNone then
    let npos := s.params.length - s.named.length
    let forwarded := s.pnames.zipIdx.map fun (n, i) =>
      let value := SExpr.ident p n
      if i < npos then value else .decl p s!"?{(s.named[i - npos]!).1}" none false value
    let lift : Choice.FirstLift := {
      key := s!"defaults:spawnBody:{adapter}", pos := p, name := adapter,
      params := (s.pnames.zip params).map fun (n, t) => { name := n, ty := t.toSTy },
      tparams := tps.map fun (n, c) =>
        { pos := p, name := n, constraint := if c then "comparable" else "type" },
      specs := (if s.fx.isEmpty then ["computes"] else s.fx) ++ ["suspends"] ++ selfTps.map ("$selfTp:" ++ ·),
      ret := ret.toSTy, body := .app p (.ident p "$spawnResult") [.app p (.ident p fname) forwarded false] false,
      binds := [], sets := [], args := [] }
    modify fun st => { st with loopFirst := st.loopFirst ++
      [{ g := "", pos := p, itemCode := .lit .void, argSet := none, lift := .ok lift }] }
    return ⟨.lit .void, ctx.retTy⟩
  let slot ← fresh packed.ty
  let name := s!"$spawnArgs{slot}"
  let cctx := { ctx with locals := { name, slot, ty := packed.ty, mutable := false } :: ctx.locals }
  let values := args[0]! :: (ts.drop 1).zipIdx.map (fun (_, i) => SExpr.app p (.ident p name) [.int p ((i + 1) : Int)] false)
  let spawned ← elabSpawn cctx p (.app p (.ident p adapter) values false)
  return ⟨.seq (.assign slot packed.e) spawned.e, spawned.ty⟩

/-- A caller-side factory for one implementation and one static declaration.
    All supplied values were evaluated before dispatch; omitted defaults are
    bound in the implementation's own type and declaration scope. -/
partial def elabSpawnDispatch (ctx : Ctx) (p : Pos) (cls fname declared : String)
    (args : List SExpr) (exp : Option Ty) : EM R := do
  let some s := ctx.sig? fname | eerr p s!"internal: no spawn signature for {fname}"
  let some root := ctx.sig? declared | eerr p s!"internal: no static spawn signature for {declared}"
  let impl := (fname.splitOn ".").headD ""
  let owner := (declared.splitOn ".").headD ""
  let cps := (ctx.types.sparams.lookup cls).getD []
  let ips := (ctx.types.sparams.lookup impl).getD []
  let rps := (ctx.types.sparams.lookup owner).getD []
  let clsArgs := cps.map fun (n, c) => Ty.param n c
  let own := (s.tparams.drop ips.length).zipIdx.map fun ((_, c), i) => (s!"$spawnOwn{i}", c)
  let ownArgs := own.map fun (n, c) => Ty.param n c
  let isigma := (ips.map (·.1)).zip (ctx.types.upArgs cls clsArgs impl) ++
    ((s.tparams.drop ips.length).map (·.1)).zip ownArgs
  let rsigma := (rps.map (·.1)).zip (ctx.types.upArgs cls clsArgs owner) ++
    ((root.tparams.drop rps.length).map (·.1)).zip ownArgs
  let ret := root.ret.subst rsigma
  let fullParams := Ty.struct cls clsArgs :: (s.params.drop 1).map (·.subst isigma)
  let npos := s.params.length - s.named.length
  let namedArgs := args.filterMap fun
    | .decl q n _ _ rhs => if n.startsWith "?" then some (q, (n.drop 1).toString, rhs) else none
    | _ => none
  for ((q, n, _), i) in namedArgs.zipIdx do
    if (namedArgs.take i).any (·.2.1 == n) then eerr q s!"?{n} is given twice"
  let named := namedArgs.map fun (_, n, rhs) => (n, rhs)
  let positional := args.filter fun | .decl _ n .. => !n.startsWith "?" | _ => true
  let given := List.range npos ++ (s.named.zipIdx.filterMap fun ((n, _), j) =>
    if named.any (·.1 == n) then some (npos + j) else none)
  let flags : Nat := (if ctx.inRepeat then 1 else 0) + (if ctx.inDefer then 2 else 0) +
    (if ctx.inDefaultCheck then 4 else 0)
  let key := s!"defaults:spawn:{cls}:{fname}:{declared}:{reprStr given}:{reprStr ctx.defaults}:{flags}"
  let name := s!"{cls}.$dispatchDefaultsSpawn{key.hash}"
  let actual := given.filterMap fun i => if i < npos then positional[i]? else
    (s.named[i - npos]?).bind fun (n, _) => named.lookup n
  if (ctx.sig? name).isSome then return ← elabApp ctx p (.ident p name) actual false exp
  let types := given.map fun i => fullParams[i]!
  let used := (ret :: types).flatMap Ty.params
  let tps := (cps ++ own).filter fun (n, _) => used.contains n
  let forwarded := given.map fun i =>
    let value := SExpr.ident p s.pnames[i]!
    if i < npos then value else .decl p s!"?{(s.named[i - npos]!).1}" none false value
  let adapter := s!"{cls}.$spawnBody{key.hash}"
  let stack := ctx.defaults.map fun (f, n) => SExpr.tuple p [.str p [.text f], .str p [.text n]]
  let lift : Choice.FirstLift := {
    key, pos := p, name,
    params := given.map fun i => { name := s.pnames[i]!, ty := fullParams[i]!.toSTy },
    tparams := tps.map fun (n, c) =>
      { pos := p, name := n, constraint := if c then "comparable" else "type" },
    specs := ["transacts"] ++ cps.map (fun (n, _) => "$selfTp:" ++ n),
    ret := (Ty.struct "task" [ret]).toSTy,
    body := .app p (.ident p "$defaultContext")
      [.block p stack, .int p (flags : Int), .app p (.ident p "$spawnBound")
        (.ident p fname :: .ident p adapter :: forwarded) false] false,
    binds := [], sets := [], args := [] }
  modify fun st => { st with loopFirst := st.loopFirst ++
    [{ g := "", pos := p, itemCode := .lit .void, argSet := none, lift := .ok lift }] }
  noteFx p s.fx (some fname)
  return ⟨.prim .userErr [], exp.getD (.struct "task" [ret])⟩

/-- Supply only the already-evaluated arguments to a selected implementation.
    Omitted defaults run in a forwarding helper, after dispatch has refined
    or opened the receiver's types. The helper's default stack preserves
    recursive-default checks across generated function boundaries. -/
partial def elabDefaultDispatch (ctx : Ctx) (p : Pos) (fname : String)
    (args : List SExpr) (bracket : Bool) (exp : Option Ty) : EM R := do
  let some s := ctx.sig? fname | eerr p s!"internal: no signature for {fname}"
  let npos := s.params.length - s.named.length
  let namedArgs := args.filterMap fun
    | .decl q n _ _ rhs => if n.startsWith "?" then some (q, (n.drop 1).toString, rhs) else none
    | _ => none
  for ((q, n, _), i) in namedArgs.zipIdx do
    if (namedArgs.take i).any (·.2.1 == n) then eerr q s!"?{n} is given twice"
  let named := namedArgs.map fun (_, n, rhs) => (n, rhs)
  let omitted := s.named.filter fun (n, _) => !named.any (·.1 == n)
  if omitted.isEmpty then return ← elabApp ctx p (.ident p fname) args bracket exp
  for (n, d) in omitted do
    if d.isNone then eerr p s!"{fname} needs the argument ?{n}, which has no default"
    if ctx.defaults.contains (fname, s!"?{n}") then
      eerr p s!"the default of ?{n} of {fname} uses itself (a call of {fname} that omits ?{n})"
  let positional := args.filter fun | .decl _ n .. => !n.startsWith "?" | _ => true
  let given := (List.range npos) ++ (s.named.zipIdx.filterMap fun ((n, _), j) =>
    if named.any (·.1 == n) then some (npos + j) else none)
  let flags : Nat := (if ctx.inRepeat then 1 else 0) + (if ctx.inDefer then 2 else 0) +
    (if ctx.inDefaultCheck then 4 else 0)
  let key := s!"defaults:{fname}:{reprStr given}:{reprStr ctx.defaults}:{flags}"
  let name := s!"{fname}$dispatchDefaults{key.hash}"
  let actual := given.filterMap fun i => if i < npos then positional[i]? else
    (s.named[i - npos]?).bind fun (n, _) => named.lookup n
  if (ctx.sig? name).isSome then
    return ← elabApp ctx p (.ident p name) actual bracket exp
  let types := given.map fun i => s.params[i]!
  let used := (s.ret :: types).flatMap Ty.params
  let tps := s.tparams.filter fun (n, _) => used.contains n
  let params : List SParam := given.map fun i =>
    { name := s.pnames[i]!, ty := s.params[i]!.toSTy }
  let forwarded := given.map fun i =>
    let v := SExpr.ident p s.pnames[i]!
    if i < npos then v else SExpr.decl p s!"?{(s.named[i - npos]!).1}" none false v
  let stack := ctx.defaults.map fun (f, n) => SExpr.tuple p [.str p [.text f], .str p [.text n]]
  let body := SExpr.app p (.ident p "$defaultContext")
    [.block p stack, .int p (flags : Int), .app p (.ident p fname) forwarded bracket] false
  let lift : Choice.FirstLift := {
    key, pos := p, name, params,
    tparams := tps.map fun (n, cmp) =>
      { pos := p, name := n, constraint := if cmp then "comparable" else "type" },
    specs := ["transacts"] ++ (if s.decides then ["decides"] else []) ++
      (if s.suspends then ["suspends"] else []) ++ s.selfTps.map ("$selfTp:" ++ ·),
    ret := s.ret.toSTy, body, binds := [], sets := [], args := [] }
  modify fun st => { st with loopFirst := st.loopFirst ++
    [{ g := "", pos := p, itemCode := .lit .void, argSet := none, lift := .ok lift }] }
  noteFx p s.fx (some fname)
  let recv ← elabE ctx positional[0]! none
  -- This round only discovers the helper; it returns before Core checking.
  return ⟨.call s.idx (recv.e :: List.replicate (s.params.length - 1 + s.ndicts) (.lit .void)),
    exp.getD s.ret⟩

/-- `e.m`: `.Length` of an array or string, or a field of a struct. -/
partial def elabMember (ctx : Ctx) (p : Pos) (r : R) (m : String) (exp : Option Ty := none) : EM R := do
  match r.ty, m with
  | .arr _, "Length" => return ⟨.prim .len [r.e], .int⟩
  | .map _ _, "Length" => return ⟨.prim .len [r.e], .int⟩
  | .struct sn targs, f =>
    match fieldIndex (ctx.types.fields sn targs) f with
    | some (k, t) =>
      if ctx.types.isRefClass sn then
        -- a reference: the field of its object (#34), at the same position in
        -- every class below a class (inherited fields come first), but maybe
        -- not below an interface: then one test of the object's class each
        let ds := ctx.types.concreteBelow sn
        let pos := ds.map fun d => ((fieldIndex (ctx.types.fields d []) f).map (·.1)).getD k
        if ctx.types.isVarField sn f then noteFx p ["reads"]
        -- (where every class below has it, so does every placeholder below,
        -- even when that is not `k`: an interface listed after another,
        -- #157; and with one type in all of them, #205)
        let env := ctx.types
        let p0 := pos.headD k
        let tyOK := env.fieldTyAgrees sn targs f
        -- (not through views, whose reference has no type arguments of the
        -- object's to read the field at: each class's getter, #351)
        if tyOK && pos.all (· == p0) && !env.viewed.contains sn then return ⟨.heap (.get p0) [r.e], t⟩
        if let some d := ds.find? fun d => !env.sameCore d sn && (env.fieldAcc.idxOf? (d, f)).isNone then
          if !tyOK then
            eerr p s!"field '{f}' of {sn} has another type in {d}, which takes it from another interface, and {d} has type parameters that {sn} does not have: reading it through {sn} is not supported yet (#205)"
          eerr p s!"field '{f}' of {sn} sits at different places in the classes below it, and {d} has type parameters that {sn} does not have: reading it is not supported yet (#53, #157)"
        let x ← fresh r.ty
        let mut acc : Expr := .prim .userErr []   -- no class: unreachable
        let mut refined := false
        for (d, kd) in (ds.zip pos).reverse do
          match env.fieldAcc.idxOf? (d, f) with
          | some i =>
            -- (a class that fixes the type arguments: its getter, under the
            -- refinement, #157)
            acc := .ite (.heap (.isTag [env.tagOf d]) [.local x]) (.call (env.fieldAccBase + 2 * i) [.local x]) acc
            refined := true
          | none =>
            let yd ← fresh (.struct d (env.argsAt sn targs d))
            acc := .ite (.assign yd (.heap (.isTag [env.tagOf d]) [.local x])) (.heap (.get kd) [.local yd]) acc
        if refined then
          -- (checked against the field's type, as the refined calls need one)
          let y ← fresh t
          return ⟨.seq (.assign x r.e) (.assign y acc), t⟩
        return ⟨.seq (.assign x r.e) acc, t⟩
      if ctx.types.classes.contains sn then
        -- a class: the field of whichever option is set (inherited fields come
        -- first, so it has the same position in all of them)
        let ds := ctx.types.concreteBelow sn
        let x ← fresh r.ty
        let mut acc : Expr := .prim .userErr []   -- no option set: unreachable
        for (d, j) in (ds.zip (List.range ds.length)).reverse do
          let dargs := if d == sn then targs else []
          -- the field's position in `d` (the same in all the classes below a
          -- class, but not below an interface)
          let kd := ((fieldIndex (ctx.types.fields d dargs) f).map (·.1)).getD k
          let td ← fresh (classRepTy ctx.types d dargs)
          acc := .ite (.assign td (.prim .query [.prim (.tupGet j) [.local x]])) (.prim (.tupGet kd) [.local td]) acc
        let y ← fresh t
        return ⟨.seq (.assign x r.e) (.assign y acc), t⟩
      return ⟨.prim (.tupGet k) [r.e], t⟩
    | none =>
      if ctx.types.classes.contains sn then
        if f.startsWith "(" then
          eerr p s!"X.{f}, a qualified method, cannot be used as a value: call it with X.{f}(…) (#210)"
        -- (a method that a class below overloads is renamed, #106: one
        -- overload visible here is still a value; more are overloaded)
        let visibleOv := ((ctx.types.methodOverloads.lookup f).getD []).filter (ctx.hasMethod sn ·)
        if visibleOv.length > 1 then
          eerr p s!"'{f}' is an overloaded method of {sn}: an overloaded method cannot be used as a value (Book of Verse ch. 6)"
        let hasValue := (ctx.types.supers sn).any fun x => ctx.types.classes.contains s!"{x}${f}$fn"
        let genericMethod (m : String) : Bool :=
          match ctx.methodDecl? sn m with
          | some owner => (ctx.sig? s!"{owner}.{m}").any fun sg => sg.named.isEmpty &&
              sg.tparams.length > ((ctx.types.sparams.lookup owner).getD []).length
          | none => false
        if ctx.hasMethod sn f || (visibleOv.length == 1 && (hasValue || genericMethod visibleOv.head!)) then
          -- a method as a value (#210): an object of the value class of the
          -- nearest class that declares or overrides it (#219: an override
          -- may narrow the result), holding the receiver, of its type, or
          -- of a class further up whose type is the one expected
          let env := ctx.types
          -- (one implementation per class below, as a call needs, #70; of
          -- the overload visible here, as a class below renamed it, #106)
          let fv := if ctx.hasMethod sn f then f else visibleOv.headD f
          let roots := ctx.rootsOf sn fv
          if let some root := roots.head? then
            for d in env.concreteBelow sn do
              for o in roots do
                if ctx.implFor? d o fv != ctx.implFor? d root fv then
                  eerr p s!"{d} implements {f} separately for {root} and {o}, so the value {f} would not say which: call it as X.({root}:){f}(…) or X.({o}:){f}(…)"
          let typeOf (x : String) : Ty :=
            let cls := s!"{x}${f}$fn"
            let i := (env.info cls).ifaces.headD ""
            let σ := (((env.sparams.lookup cls).getD []).map (·.1)).zip (env.argsAt sn targs x)
            .struct i (((env.iargs.lookup (cls, i)).getD []).map (Ty.subst σ))
          let candidates := (env.supers sn).filter fun x => env.classes.contains s!"{x}${f}$fn"
          -- Fix the captured receiver before inferring an adapter from
          -- the expected function type. Tuple expansion can replace even
          -- a receiver parameter with components; `$self` pins them all.
          let methodTps (x : String) := ((env.sparams.lookup s!"{x}${f}$fn").getD []).drop
            ((env.sparams.lookup x).getD []).length
          if let some target@(.struct shape _) := exp then
            if let some (k, _) := FnValues.parseName shape then
              for x in candidates do
                for cls in [s!"{x}${f}$fn", s!"{x}${f}$fnPack", s!"{x}${f}$fnUnpack{k}"] do
                  if !env.classes.contains cls then continue
                  let some (_, selfTy, _) := (env.fields cls []).find? (·.1 == "$self") | continue
                  let receiver := Ty.struct x (env.argsAt sn targs x)
                  let some fixed := selfTy.matchArg env [] receiver | continue
                  if !(selfTy.subst fixed).eqv receiver then continue
                  let some args := fnClassArgs env cls target fixed | continue
                  let tv ← fresh r.ty
                  let nm := s!"$recv{tv}"
                  let ctx' := { ctx with locals := { name := nm, slot := tv, ty := r.ty, mutable := false } :: ctx.locals }
                  let rv ← elabConstruct ctx' p cls [] [.decl p "$self" none false (.ident p nm)]
                    (some (.struct cls args))
                  return ⟨.seq (.assign tv r.e) (← coerce p rv target), target⟩
          if genericMethod fv || candidates.any (fun x => !(methodTps x).isEmpty) then
            eerr p s!"'{f}' is a generic method of {sn}: a function type determining all its method type arguments and satisfying its bounds must be expected (#209)"
          -- (#231) wanted at a closed function type that no value class of
          -- it gives but that it fits by variance: a class made for that type,
          -- `{x}${f}$fn${k}` (the nearest class's, without type parameters),
          -- holding the receiver; asked for the first time (a placeholder,
          -- and the program is elaborated again with the class made)
          if let some t@(.struct tm tts) := exp then
            if (FnValues.parseName tm).isSome && (tts.all fun u => u.params.isEmpty) &&
                !(candidates.any fun x => typeOf x == t) then
              if let some x0 := candidates.head? then
                if ((env.sparams.lookup s!"{x0}${f}$fn").getD []).isEmpty then
                  let variantTy (c : String) : Ty :=
                    let i := (env.info c).ifaces.headD ""
                    .struct i ((env.iargs.lookup (c, i)).getD [])
                  match env.classes.find? (fun c => c.startsWith s!"{x0}${f}$fn$" && variantTy c == t) with
                  | some vc =>
                    let tv ← fresh r.ty
                    let nm := s!"$recv{tv}"
                    let ctx' := { ctx with locals := { name := nm, slot := tv, ty := r.ty, mutable := false } :: ctx.locals }
                    let rv ← elabConstruct ctx' p vc [] [.decl p "$self" none false (.ident p nm)] (some (.struct vc []))
                    return ⟨.seq (.assign tv r.e) (← coerce p rv t), t⟩
                  | none =>
                    let key := s!".{x0}${f}"
                    if !env.fnRequests.contains (key, t) && fnTyFits env (typeOf x0) t then
                      modify fun st => { st with fnNeeds := st.fnNeeds ++ [(key, t)] }
                      return ⟨.seq r.e (.prim .userErr []), t⟩
          -- A generic receiver fixes its method's signature too. Requested
          -- adapters retain its witnesses and ordinary call conversions.
          if let some target@(.struct shape _) := exp then
            if (FnValues.parseName shape).isSome then
              for x in candidates do
                if !(methodTps x).isEmpty then continue
                let receiver := Ty.struct x (env.argsAt sn targs x)
                let some (req, args) ← methodVarianceRequest ctx p x f receiver (typeOf x) target | continue
                if let some i := env.methodRequests.findIdx? (·.key == req.key) then
                  let cls := req.className i
                  let tv ← fresh r.ty
                  let nm := s!"$recv{tv}"
                  let ctx' := { ctx with locals := { name := nm, slot := tv, ty := r.ty, mutable := false } :: ctx.locals }
                  let rv ← elabConstruct ctx' p cls [] [.decl p "$self" none false (.ident p nm)]
                    (some (.struct cls args))
                  return ⟨.seq (.assign tv r.e) (← coerce p rv target), target⟩
                modify fun st => { st with methodNeeds := FnValues.mergeMethodRequests st.methodNeeds [req] }
                return ⟨.seq r.e (.prim .userErr []), target⟩
          let some x := (candidates.find? fun x => exp == some (typeOf x)).orElse fun _ => candidates.head?
            | eerr p s!"'{f}' is a method of {sn} that cannot be used as a value: call it with {f}(…) (a method with named parameters is not a value, #210)"
          let cls := s!"{x}${f}$fn"
          let xargs := env.argsAt sn targs x
          let t ← fresh r.ty
          let nm := s!"$recv{t}"
          let ctx' := { ctx with locals := { name := nm, slot := t, ty := r.ty, mutable := false } :: ctx.locals }
          let rv ← elabConstruct ctx' p cls [] [.decl p "$self" none false (.ident p nm)] (some (.struct cls xargs))
          let own := typeOf x
          return ⟨.seq (.assign t r.e) (← coerce p rv own), own⟩
        if visibleOv.length == 1 then
          eerr p s!"'{f}' is a method of {sn} that cannot be used as a value: call it with {f}(…) (a method with named parameters is not a value, #210)"
        eerr p s!"class {sn} has no field '{f}'"
      eerr p s!"struct {sn} has no field '{f}'"
  | t, m => eerr p s!"{t.show} has no member '{m}'"

/-- A default's declaration scope, actual home-class arguments and cycle
    check, shared by ordinary and choice-lifted construction operands. -/
partial def elabFieldDefault (ctx : Ctx) (p : Pos) (name : String) (tas : List Ty)
    (f : String) (t : Ty) (d : SExpr) : EM Expr := do
  let home := (ctx.types.defaultHome.lookup (name, f)).getD name
  let hσ := (((ctx.types.sparams.lookup home).getD []).map (·.1)).zip (ctx.types.argsAt name tas home)
  let dctx := { ctx with locals := [], selfClass := none, types := { ctx.types with tvars := hσ } }
  if dctx.defaults.contains (name, f) then
    eerr p s!"the default of field '{f}' of {name} depends on itself"
  fxAt p (do coerce p (← elabE { dctx with defaults := (name, f) :: dctx.defaults } d (some t)) t)

/-- `name{F := e, …}` or `name(t₁, …){F := e, …}`: the struct's fields in
    declaration order; omitted fields take their default values. The type
    arguments of a parametric struct are written, or are those of the
    expected type. -/
partial def elabConstruct (ctx : Ctx) (p : Pos) (name : String) (targs : List STy) (args : List SExpr)
    (exp : Option Ty) : EM R := do
  if (ctx.types.structs.lookup name).isNone then eerr p s!"unknown struct '{name}'"
  let ty ← match targs, exp with
    | [], some (.struct n ts) => if n == name then pure (.struct n ts) else resolveTy ctx.types p (.name name)
    | [], _ => resolveTy ctx.types p (.name name)
    | ts, _ => resolveTy ctx.types p (.app name ts)
  let tas := match ty with | .struct _ tas => tas | _ => []
  let fs := ctx.types.fields name tas
  let given ← args.mapM fun a => match a with
    | .decl _ f none false rhs => pure (f, rhs)
    | a => eerr a.pos "a struct field is given as Name := value"
  for (f, _) in given do
    if (fs.find? (·.1 == f)).isNone then eerr p s!"struct {name} has no field '{f}'"
  -- (only the first would be evaluated)
  if let some f := (given.map (·.1)).find? (fun f => (given.filter (·.1 == f)).length > 1) then
    eerr p s!"field '{f}' of {name} is given twice"
  let es ← fs.mapM fun (f, t, dflt) => do
    match given.lookup f, dflt with
    | some rhs, _ => coerce p (← elabE ctx rhs (some t)) t
    | none, some d =>
      elabFieldDefault ctx p name tas f t d
    | none, none => eerr p s!"field '{f}' of {name} has no default value and must be given"
  if ctx.types.classes.contains name then
    let i := ctx.types.info name
    if i.isIface then eerr p s!"{name} is an interface: it cannot be constructed"
    if i.isAbstract then eerr p s!"{name} is <abstract>: it cannot be constructed"
    -- a new object (#34); one that can change, or has an identity, allocates
    if ctx.types.isRefClass name then
      if ctx.types.isUnique name || fs.any (fun (f, _, _) => ctx.types.isVarField name f) then
        noteFx p ["allocates"]
      -- then the `block:` clauses of its class chain, from the top
      let chain := ((ctx.types.supers name).filter fun d => !(ctx.types.info d).isIface).reverse
      let blocks := chain.filterMap fun d => (ctx.sig? s!"{d}.$block").map (d, ·)
      if blocks.isEmpty then
        -- a parametric class's object goes through a temporary of its type,
        -- which gives the checker its type arguments (#39)
        -- (and so does a pinned class's, whose pins may be on more type
        -- arguments than the type it is used at, #209)
        if tas.isEmpty && (ctx.types.corePins name).isEmpty then return ⟨.heap (.new (ctx.types.tagOf name)) es, ty⟩
        let x ← fresh ty
        return ⟨.assign x (.heap (.new (ctx.types.tagOf name)) es), ty⟩
      let x ← fresh ty
      let mut calls : List Expr := []
      for (d, s) in blocks do
        noteFx p s.fx (some s!"constructs {name}, whose block: (in {d})")
        if s.tparams.isEmpty then
          calls := calls ++ [.call s.idx [.local x]]
        else
          -- a parametric class's `block:` is generic (#39): called as a
          -- method, on the new object at its type arguments as a `d`
          let self := s!"$new{x}"
          let dty := Ty.struct d (ctx.types.upArgs name tas d)
          let ctx' := { ctx with locals := { name := self, slot := x, ty := dty, mutable := false } :: ctx.locals }
          let rc ← elabApp ctx' p (.ident p s!"{d}.$block") [.ident p self] false none
          calls := calls ++ [rc.e]
      return ⟨.seq (.assign x (.heap (.new (ctx.types.tagOf name)) es)) (calls.foldr .seq (.local x)), ty⟩
    let x ← fresh ty
    return ⟨.assign x (classWrap ctx.types name name (.prim .mkTup es)), ty⟩
  -- A struct's fields may need their expected types (empty arrays/options
  -- and computed defaults). Preserve the resolved instance before a Core
  -- consumer, such as tuple projection, has to infer its operand's type.
  let x ← fresh ty
  return ⟨.assign x (.prim .mkTup es), ty⟩

/-- `map{k₁ => v₁, …}`: entries are evaluated in order; a key given twice
    keeps its last value, at the position of its last occurrence (Book of
    Verse §9.3). -/
partial def elabMapLit (ctx : Ctx) (p : Pos) (entries : List (SExpr × SExpr)) (exp : Option Ty) : EM R := do
  let (kt?, vt?) := match exp with
    | some (.map k v) => (some k, some v)
    | _ => (none, none)
  match entries with
  | [] =>
    match kt?, vt? with
    | some k, some v => return ⟨.lit Value.emptyArray, .map k v⟩
    | _, _ => eerr p "the type of an empty map{} must be given (e.g. M:[string]int = map{})"
  | (k0, v0) :: _ =>
    let rk0 ← elabE ctx k0 kt?
    let rv0 ← elabE ctx v0 vt?
    let kt := kt?.getD rk0.ty
    if !kt.comparable ctx.types then eerr p (notComparable ctx.types kt "a map key")
    let vt0 := vt?.getD rv0.ty
    let mut rs : Array (SExpr × R × SExpr × R) := #[]
    for (k, v) in entries do
      rs := rs.push (k, ← elabE ctx k (some kt), v, ← elabE ctx v (some vt0))
    -- the values' type: the expected one (or the first's) when every value
    -- converts to it, else their join, as for an array literal (#67)
    let vt ← match ← tryCatch (some <$> rs.toList.mapM fun (_, _, v, rv) => coerce v.pos rv vt0) (fun _ => pure none) with
      | some _ => pure vt0
      | none => rs.toList.foldlM (fun acc (_, _, v, rv) => do
          match joinTy (← get).env acc rv.ty vt? with
          | some j => pure j
          | none => eerr v.pos s!"the values of this map have different types: {acc.show} and {rv.ty.show}") rv0.ty
    let mut steps : Array Expr := #[]
    let mut slots : Array (Nat × Nat) := #[]
    for (k, rk, v, rv) in rs do
      let tk ← fresh kt
      let tv ← fresh vt
      steps := steps.push (.assign tk (← coerce k.pos rk kt))
      steps := steps.push (.assign tv (← coerce v.pos rv vt))
      slots := slots.push (tk, tv)
    let n := slots.size
    let items := (List.range n).map fun i =>
      let (tk, tv) := slots[i]!
      let later := ((List.range n).filter (· > i)).map fun j => Expr.prim .ne [.local tk, .local slots[j]!.1]
      let cond := later.foldr Expr.seq (.lit (.logic true))
      Expr.ite cond (.prim .mkArr [.prim .mkTup [.local tk, .local tv]]) (.lit Value.emptyArray)
    let built := Expr.prim .flatten [.prim .mkArr items]
    return ⟨steps.toList.foldr Expr.seq built, .map kt vt⟩

partial def elabCase (ctx : Ctx) (p : Pos) (scrut : SExpr) (arms : List (Option SExpr × SExpr))
    (exp : Option Ty) : EM R := do
  let rs := widenR ctx.types (← elabE ctx scrut none)
  match rs.ty with
  | .int | .logic | .char | .char32 | .arr .char | .enum _ => pure ()
  | t => eerr p s!"case works on int, logic, char, char32, string and enums, not {t.show}"
  let t ← fresh rs.ty
  let elabArms : List (Option SExpr × SExpr) → EM (Expr × Ty) := fun arms => do
    let mut results : Array (Option Expr × R) := #[]
    for (pat, v) in arms do
      let rv ← elabE ctx v exp
      match pat with
      | none => results := results.push (none, rv)
      | some pe =>
        let rp ← elabE ctx pe (some rs.ty)
        if rp.ty != rs.ty then eerr pe.pos s!"pattern of type {rp.ty.show} for a value of type {rs.ty.show}"
        -- (a pattern is tested in a condition, #156)
        if Suspend.hasSusp (fun f => ctx.sigs.any fun s => s.idx == f && s.suspends) rp.e then
          eerr pe.pos "a case pattern cannot suspend: it is tested as a condition (#156)"
        results := results.push (some rp.e, rv)
    let mut ty : Ty := .never
    for (_, rv) in results do ty ← join p ty rv.ty exp
    let hasDefault := results.any (·.1.isNone)
    -- an enum case that names every enumerator needs no `_` (Book of Verse
    -- §7.6), unless the enum is open: it may gain values (ch. 9)
    let exhaustive := match rs.ty with
      | .enum n =>
        !ctx.types.openEnums.contains n &&
        let k := ((ctx.types.enums.lookup n).getD []).length
        (List.range k).all fun i => results.any fun (pat, _) => match pat with
          | some (.lit (.int j)) => j == i
          | _ => false
      | _ => false
    let mut acc : Expr ← if hasDefault then pure (.lit .void) else
      if exhaustive then pure (.prim .userErr [])   -- unreachable
      else if ctx.canFail then pure (.prim .fail [])
      else match rs.ty with
        | .enum n =>
          if ctx.types.openEnums.contains n then
            eerr p s!"a case on the open enum {n} needs _ (it may gain values), unless failure is allowed (e.g. in a <decides> function)"
          else eerr p "a case without _ is only allowed where failure is (e.g. a <decides> function), or on an enum when every value is named"
        | _ => eerr p "a case without _ is only allowed where failure is (e.g. a <decides> function), or on an enum when every value is named"
    for (pat, rv) in results.reverse do
      let v ← coerce p rv ty
      match pat with
      | none => acc := v
      | some pe => acc := .ite (p2 .eq (.local t) pe) v acc
    return (acc, ty)
  let (body, ty) ← elabArms arms
  return ⟨.seq (.assign t rs.e) body, ty⟩
end

/-- (#283) `elabStmt` of a body whose calls of overloaded functions with
    several values are resolved first: an elaboration for types, each call
    as written (`ovForTypes`), noting the overload each takes; then each
    call its chosen overload's inlined call (`ovChosen`). -/
def elabBodyOv (ctx : Ctx) (body : SExpr) (ret : Option Ty) (st0 : ESt) : Except String ((R × Ctx) × ESt) := do
  if !Choice.anyE (fun | .app _ (.ident _ "$inlineOv") _ false => true | _ => false) body then
    return ← (elabStmt ctx body ret).run st0
  let ((_, _), stT) ← (elabStmt { ctx with typeOnly := true } (ovForTypes body) ret).run st0
  (elabStmt ctx (ovChosen stT.ovPicks body) ret).run st0

/-- An elaborated program and the certificate under which it type-checks:
    `prog.check`, `prog.checkTypes sigs slotTys` and `prog.checkControl` hold,
    so `Prog.accepted` applies to it. -/
structure Compiled where
  prog    : Prog
  sigs    : Sigs
  slotTys : List (List VTy)
  /-- Pure mutual groups that retain the eager polymorphic-recursion path. -/
  eagerNeeds : List String := []
  /-- Functions wanted as values at closed function types no class of
      theirs gives (#214): the program is elaborated again, with them. -/
  fnNeeds : List (String × Ty) := []
  methodNeeds : List FnValues.MethodRequest := []
  /-- Branches of casts that refine type arguments, to lift (#243): the
      program is elaborated again, with them. -/
  castNeeds : List Refine.Lift := []
  /-- Lazily taken calls whose effects need functions of their own (#246):
      the program is elaborated again, with them. -/
  loopNeeds : List Choice.FirstLift := []
  /-- Classes with a class parent that list an interface at type arguments
      that are not a prefix of their own (#351): the program is elaborated
      again, with hidden fields for all of their type parameters. -/
  witnessNeeds : List String := []

/-- Names a type parameter cannot have. -/
def typeNames : List String :=
  ["int", "logic", "char", "string", "void", "float", "rational", "any", "comparable", "type", "subtype"]

/-- The type parameters of a generic function or a parametric struct: name,
    and whether declared `subtype(comparable)`. -/
def checkTParams (env : TyEnv) (tps : List TParam) : Except String (List (String × Bool)) := do
  let mut out : Array (String × Bool) := #[]
  for tp in tps do
    if out.any (·.1 == tp.name) then
      throw s!"{tp.pos.show}: type parameter {tp.name} is declared twice (several constraints on one type parameter are not supported)"
    if typeNames.contains tp.name || (env.structs.lookup tp.name).isSome ||
        (env.enums.lookup tp.name).isSome then
      throw s!"{tp.pos.show}: type parameter {tp.name} has the name of a type"
    match tp.constraint with
    | "type" => out := out.push (tp.name, false)
    | "comparable" => out := out.push (tp.name, true)
    | c => throw s!"{tp.pos.show}: unknown constraint subtype({c}) (openverse supports {tp.name}:type and {tp.name}:subtype(comparable))"
  return out.toList

/-- How a program is compiled from the command line: its shell arguments,
    bound to `Args : []string` (unless the program defines `Args`), and an
    expression to run instead of `Main`. -/
structure Options where
  profile : SourceProfile := .full
  eagerRequests : List String := []
  args : Option (List String) := none
  entry : Option SExpr := none
  /-- Functions wanted as values at closed function types no class of
      theirs gave in an earlier elaboration (#214): a class for each. -/
  fnRequests : List (String × Ty) := []
  methodRequests : List FnValues.MethodRequest := []
  /-- On an internal error (an elaborated function the checker rejects),
      also print that function's Verse Core, its slot types and signature,
      for a bug report (`OPENVERSE_DEBUG=1`). -/
  debug : Bool := false
  /-- Branches of casts that refine type arguments, found in an earlier
      elaboration (#243): a function for each. -/
  castRequests : List Refine.Lift := []
  /-- Lazily taken calls whose effects need functions of their own, found
      in an earlier elaboration (#246). -/
  loopRequests : List Choice.FirstLift := []
  /-- Classes whose type parameters all get hidden fields, found in an
      earlier elaboration (#351, `Compiled.witnessNeeds`). -/
  witnessAll : List String := []

/-- A class or interface definition, as parsed. -/
structure CDef where
  pos : Pos
  name : String
  tps : List TParam
  specs : List String
  parents : List String
  /-- Each parent's type arguments (#39), in terms of this class's type parameters. -/
  parentArgs : List (List STy) := []
  isIface : Bool
  fields : List (String × STy × Option SExpr × Bool)
  overrides : List String
  methods : List STop

/-- An interface's Verse Core type arguments at `args`, in source types (as
    `TyEnv.coreArgs` has them, #53): those it gives the parent interface it
    lists with the most, in turn, then its other type parameters
    (`c2(t) := interface(container([]t))` at `int` gives `[]int, int`). -/
partial def CDef.ifaceCoreS (cdefs : List CDef) (i : CDef) (args : List STy) : List STy :=
  let σ := i.tps.map (·.name) |>.zip args
  let pas := (i.parents.zip i.parentArgs).filterMap fun (q, qa) =>
    match cdefs.find? (·.name == q) with
    | some qd => let ca := CDef.ifaceCoreS cdefs qd qa; if ca.isEmpty then none else some ca
    | none => none
  let longest := pas.foldl (fun b a => if b.length < a.length then a else b) []
  if longest.isEmpty then args else
  let others := i.tps.filter fun tp => !longest.any fun | .name v => v == tp.name | _ => false
  (longest ++ others.map fun tp => STy.name tp.name).map (·.substNames σ)

/-- Constructor functions (#11, Book of Verse ch. 10). `K<constructor>(ps) :=
    c:` with items becomes two functions with K's parameters and effects:
    - `K$init` runs the items in order and gives the fields they set, as the
      struct `K$fields` (or nothing). An initializer `F := e` binds `F$v`, a
      `let:` its declarations, and a `block:` runs. A delegation
      `D<constructor>(args)` calls `D$init(args)` and takes D's fields.
    - `K` constructs `c` from them, the other fields taking their defaults
      (so `c`'s own `block:` clauses run last).
    A constructor sees no `Self`. -/
def expandCtors (ctors : List (Pos × String × List SParam × List TParam × List String × String × List SExpr))
    (cdef? : String → Option CDef) (fullOf : String → List (String × STy × Option SExpr × Bool))
    (supers : String → List String) (targsOf : String → List STy)
    (allTargs : List (String × List STy)) : Except String (List STop) := do
  let directOf (items : List SExpr) : List (Pos × String) := items.filterMap fun
    | .decl p f none false _ => some (p, f)
    | _ => none
  let delegsOf (items : List SExpr) : List (Pos × String) := items.filterMap fun
    | .app p (.ident _ d) _ _ => if d.startsWith "$ctor:" then some (p, (d.drop "$ctor:".length).toString) else none
    | _ => none
  -- the checks of each constructor on its own
  -- overloaded constructors (Book of Verse ch. 10, #74): one class, and the
  -- same fields, so a delegation to any of them sets the same ones
  for ((p, k, _, _, _, c, _), i) in ctors.zip (List.range ctors.length) do
    if let some (_, _, _, _, _, c', _) := (ctors.take i).find? (·.2.1 == k) then
      if c' != c then throw s!"{p.show}: the overloads of constructor {k} construct {c'} and {c}: they must construct one class"
      -- (up to the names of their type parameters: each renamed by its place)
      let norm (j : Nat) : String :=
        let ts := ((allTargs.drop j).head?.map (·.2)).getD []
        let tps := ((ctors.drop j).head?.map fun (_, _, _, t, _, _, _) => t).getD []
        let vs := (ts.flatMap STy.names).eraseDups.filter fun n => tps.any (·.name == n)
        let ρ := (vs.zip (List.range vs.length)).map fun (n, q) => (n, STy.name s!"${q}")
        reprStr (ts.map (·.substNames ρ))
      let mine := (List.range ctors.length).filter fun j => ((ctors.drop j).head?.map (·.2.1)) == some k
      if (mine.map norm).eraseDups.length > 1 then
        throw s!"{p.show}: the overloads of constructor {k} construct {c} at different type arguments: they must construct one type"
  for ((p, k, ps, tps, _, c, items), ci) in ctors.zip (List.range ctors.length) do
    let some cd := cdef? c | throw s!"{p.show}: constructor {k}: {c} is not a class"
    if cd.isIface then throw s!"{p.show}: constructor {k}: {c} is an interface"
    -- a parametric class's constructor names its type arguments, `:= box(t):`
    let targs := ((allTargs.drop ci).head?.map (·.2)).getD (targsOf k)
    if cd.tps.length != targs.length then
      if cd.tps.isEmpty then throw s!"{p.show}: constructor {k}: {c} takes no type arguments"
      else if targs.isEmpty then
        throw s!"{p.show}: constructor {k}: {c} takes {cd.tps.length} type argument(s): write {c}(…) after :="
      else throw s!"{p.show}: constructor {k}: {c} takes {cd.tps.length} type argument(s), not {targs.length}"
    -- a call infers the constructor's type parameters from its arguments
    if let some tp := tps.find? fun tp => !ps.any (·.ty.mentions tp.name) then
      throw s!"{p.show}: the type parameter {tp.name} of {k} appears in none of its parameters, so a call could not infer it"
    let direct := directOf items
    for ((fp, f), i) in direct.zip (List.range direct.length) do
      if !(fullOf c).any (·.1 == f) then throw s!"{fp.show}: {k}: {c} has no field {f}"
      if (direct.take i).any (·.2 == f) then throw s!"{fp.show}: {k} sets {f} twice"
    match delegsOf items with
    | [] => pure ()
    | [(dp, d)] =>
      let some (_, _, _, _, _, dc, _) := ctors.find? (·.2.1 == d)
        | throw s!"{dp.show}: {d} is not a constructor function"
      if !(supers c).contains dc then
        throw s!"{dp.show}: {k} constructs {c}, and {d} constructs {dc}, which is not {c} or a class above it"
      if dc == c && !direct.isEmpty then
        throw s!"{dp.show}: {k} delegates to {d}, which constructs {c} itself and so sets its fields: {k} cannot set fields too"
      -- (the Book: a subclass's fields first, then the parent's constructor)
      let dIdx := items.findIdx? fun | .app _ (.ident _ x) _ _ => x.startsWith "$ctor:" | _ => false
      let late := items.zip (List.range items.length) |>.filterMap fun
        | (.decl fp f none false _, j) => if dIdx.any (· < j) then some (fp, f) else none
        | _ => none
      if let some (fp, f) := late.head? then
        throw s!"{fp.show}: {k} sets {f} after delegating to {d}: set the fields of {c} first, then delegate"
    | _ :: (dp, _) :: _ => throw s!"{dp.show}: {k} delegates to more than one constructor"
  -- the fields each sets: its own, and its delegate's
  -- the fields each name's constructors set (#80, overloads: all their
  -- fields; one that does not set a field gives it its default, below): the
  -- least fixpoint of their own and their delegates'
  let names := (ctors.map (·.2.1)).eraseDups
  let overloaded (k : String) : Bool := (ctors.filter (·.2.1 == k)).length > 1
  let mut setBy : List (String × List String) := names.map fun k =>
    (k, ((ctors.filter (·.2.1 == k)).flatMap fun (_, _, _, _, _, _, items) => (directOf items).map (·.2)).eraseDups)
  for _ in [0:ctors.length + 1] do
    let mut changed := false
    for (_, k, _, _, _, _, items) in ctors do
      if let some (_, d) := (delegsOf items).head? then
        if d != k then
          let cur := (setBy.lookup k).getD []
          let add := ((setBy.lookup d).getD []).filter (!cur.contains ·)
          if !add.isEmpty then
            setBy := setBy.map fun (n, fs) => if n == k then (n, fs ++ add) else (n, fs)
            changed := true
    if !changed then break
  -- a delegation cycle through names that are not overloaded never ends (one
  -- through an overloaded name is resolved by its arguments, and may)
  for (p, k, _, _, _, _, items) in ctors do
    if overloaded k then continue
    let next (x : String) : Option String :=
      if overloaded x then none else
      (ctors.find? (·.2.1 == x)).bind fun (_, _, _, _, _, _, its) => ((delegsOf its).map (·.2)).head?
    let mut cur := next k
    let mut onCycle := false
    let mut intoCycle := false
    let mut seen : List String := []
    for _ in [0:ctors.length] do
      match cur with
      | some x =>
        if x == k then onCycle := true; break
        if seen.contains x then intoCycle := true; break
        seen := seen ++ [x]
        cur := next x
      | none => break
    let d := ((delegsOf items).map (·.2)).headD k
    if onCycle then throw s!"{p.show}: {k} delegates to itself, through {d}"
    if intoCycle then throw s!"{p.show}: {k} delegates to {d}, which delegates in a cycle"
  for (p, k, _, _, _, _, items) in ctors do
    let mine := (directOf items).map (·.2) ++ (((delegsOf items).head?.bind fun (_, d) => setBy.lookup d).getD [])
    if let some f := mine.find? fun f => (mine.filter (· == f)).length > 1 then
      throw s!"{p.show}: {k} sets {f} twice: itself, and by delegating"
  for (p, k, _, _, _, c, items) in ctors do
    let mine := (directOf items).map (·.2) ++ (((delegsOf items).head?.bind fun (_, d) => setBy.lookup d).getD [])
    if let some (f, _) := (fullOf c).find? fun (f, _, d, _) => d.isNone && !mine.contains f then
      throw s!"{p.show}: {k} does not set {f}, a field of {c} without a default"
  -- the functions
  let mut out : Array STop := #[]
  for ((p, k, ps, tps, effs, c, items), ci) in ctors.zip (List.range ctors.length) do
    let fs := (setBy.lookup k).getD []
    let fieldsTy := s!"{k}$fields"
    -- the class's type parameters are the archetype's type arguments, which
    -- may mention the constructor's own (a generic constructor, `where`)
    let targs := ((allTargs.drop ci).head?.map (·.2)).getD (targsOf k)
    let ctps : List TParam := ((cdef? c).map (fun cd => cd.tps)).getD []
    let σ : List (String × STy) := (ctps.map (fun tp => tp.name)).zip targs
    let tyOf (f : String) : STy :=
      let t0 : STy := (((fullOf c).find? (·.1 == f)).map (·.2.1)).getD (.name "void")
      t0.substNames σ
    -- (K$fields is parametric over the type parameters the class's type
    -- arguments mention, in order: the same for every overload of K)
    let sparams : List TParam := ((targs.flatMap STy.names).eraseDups).filterMap fun n => tps.find? (·.name == n)
    let tpTys : List STy := sparams.map fun tp => STy.name tp.name
    let fieldsSTy : STy := if sparams.isEmpty then .name fieldsTy else .app fieldsTy tpTys
    if !fs.isEmpty && !out.any (fun | .const _ n _ _ => n == fieldsTy | _ => false) then
      out := out.push (.const p fieldsTy none (.structDef p sparams (fs.map fun f => (f, tyOf f, none, false))))
    let mut body : Array SExpr := #[]
    let mut di := 0
    for it in items do
      match it with
      | .decl ip f none false e => body := body.push (.decl ip s!"{f}$v" (some (tyOf f)) false e)
      | .app ip (.ident _ "$let") [.block _ ds] _ =>
        for d in ds do
          match d with
          | .decl .. => body := body.push d
          | _ => throw s!"{ip.show}: a let: in a constructor has only declarations"
      | .app ip (.ident _ d0) args br =>
        let d := (d0.drop "$ctor:".length).toString
        let call := SExpr.app ip (.ident ip s!"{d}$init") args br
        match (setBy.lookup d).getD [] with
        | [] => body := body.push call
        | dfs =>
          let tmp := s!"$deleg{di}"
          di := di + 1
          body := body.push (.decl ip tmp none false call)
          for f in dfs do
            body := body.push (.decl ip s!"{f}$v" (some (tyOf f)) false (.member ip (.ident ip tmp) f))
      | it => body := body.push (.app p (.ident p "$nofail") [it] false)   -- a `block:` clause
    -- the name's fields this overload does not set (another overload does):
    -- their defaults, as construction would give them
    let mine := (directOf items).map (·.2) ++ (((delegsOf items).head?.bind fun (_, d) => setBy.lookup d).getD [])
    for f in fs.filter (!mine.contains ·) do
      if let some (_, _, some d, _) := (fullOf c).find? (·.1 == f) then
        -- (in a function of its own: the default sees no parameter of K)
        if tps.any (fun tp => (tyOf f).mentions tp.name) then
          throw s!"{p.show}: {k} leaves {f} to another overload, and its default's type mentions a type parameter of {k}: give {f} in every overload of a generic constructor"
        let helper := s!"{k}$default${f}"
        if !out.any (fun | .fn _ n .. => n == helper | _ => false) then
          -- (its effects are its code's, inferred as a `block:`'s are: every
          -- overload that leaves F to it then pays for what it does)
          out := out.push (.fn p helper [] [] [] (tyOf f) d)
        body := body.push (.decl p s!"{f}$v" (some (tyOf f)) false (.app p (.ident p helper) [] false))
    let initRet : SExpr :=
      if fs.isEmpty then .block p []
      else .construct p fieldsTy tpTys (fs.map fun f => .decl p f none false (.ident p s!"{f}$v"))
    out := out.push (.fn p s!"{k}$init" ps tps effs (if fs.isEmpty then .name "void" else fieldsSTy)
      (.block p (body.toList ++ [initRet])))
    let args := ps.map fun prm =>
      if prm.named then SExpr.decl p s!"?{prm.name}" none false (.ident p prm.name) else .ident p prm.name
    let callInit := SExpr.app p (.ident p s!"{k}$init") args (effs.contains "decides")
    let kbody : SExpr :=
      if fs.isEmpty then .block p [callInit, .construct p c targs []]
      else .block p [.decl p "$fields" none false callInit,
        .construct p c targs (fs.map fun f => .decl p f none false (.member p (.ident p "$fields") f))]
    -- (an abstract class is only constructed by delegating to its constructors)
    if !((cdef? c).map (·.specs.contains "abstract")).getD false then
      out := out.push (.fn p k ps tps effs (if targs.isEmpty then .name c else .app c targs) kbody)
  return out.toList

/-- The concurrency helpers (#156), written in Verse: the scheduler's
    state (the clock, in ticks of 1/30 s, and the earliest tick a sleeping
    task waits for), and `Sleep`'s frame with its `new`, `init` and `resume`.
    `Sleep` itself is a stub that only marks the suspension point: the
    lowering (`Suspend.lean`) calls the others in its place. -/
def concPrelude : String := "
sched := class:
    var Now:int = 0
    var Next:int = -1
    var Progress:logic = false
    var Head:?int = false
    var Tail:?int = false
    var Dead:logic = false
    var CancelCur:logic = false
    var CurTask:taskBase = taskBase{}
taskBase := class:
    var Done:logic = false
    var Sch:?sched = false
    var Cancelled:logic = false
    var Running:logic = false
    var Root:?int = false
    var CancelReq:logic = false
task(t:type) := class(taskBase):
    var Result:?t = false
waitf := class:
    var Pc:int = 0
    var T:taskBase
waitNew(X:taskBase):waitf = waitf{T := X}
waitInit(F:waitf, X:taskBase):void =
    set F.Pc = 0
    set F.T = X
waitResume(F:waitf, C:sched):int =
    if (F.T.Cancelled?):
        set C.CancelCur = true
        return 0
    if (F.T.Done?) then return 1
    if (F.Pc = 0):
        set F.Pc = 1
        set F.T.Sch = option{C}
    0
WaitDone(X:taskBase)<suspends><computes>:void = {}
Await(T:task(t) where t:type)<suspends>:t =
    WaitDone(T)
    if (R := T.Result?) then R else Err()
spawnMark(A:[]void)<computes>:void = {}
cancelMark(X:taskBase)<suspends><computes>:void = {}
branchMark(A:[]void)<computes>:void = {}
evrec(t:type) := class(taskBase):
    var Got:?t = false
    var Next:?evrec(t) = false
event(t:type) := class:
    var Head:?evrec(t) = false
    var Tail:?evrec(t) = false
    Signal(X:t):void =
        if (Head?) then signalAll(Self, X)
signalAll(E:event(t), X:t where t:type):void =
    var Cur:?evrec(t) = E.Head
    set E.Head = false
    set E.Tail = false
    loop:
        if (W := Cur?):
            set W.Got = option{X}
            set W.Done = true
            if (S := W.Sch?) then set S.Progress = true
            set Cur = W.Next
        else:
            break
EvAwait(E:event(t) where t:type)<suspends>:t =
    loop:
        if (H := E.Head?, H.Done?):
            set E.Head = H.Next
        else:
            break
    if (E.Head?) {} else { set E.Tail = false }
    W := evrec(t){}
    if (L := E.Tail?) then set L.Next = option{W} else set E.Head = option{W}
    set E.Tail = option{W}
    defer:
        set W.Done = true
    WaitDone(W)
    if (V := W.Got?) then V else Err()
sticky_event(t:type) := class(event(t)):
    var Last:?t = false
    Signal<override>(X:t):void =
        set Last = option{X}
        if (Head?) then signalAll(Self, X)
StickyAwait(E:sticky_event(t) where t:type)<suspends>:t =
    if (V := E.Last?) then V else EvAwait(E)
sleep := class:
    var Pc:int = 0
    var Secs:float = 0.0
    var Wake:int = 0
sleepNew(S:float):sleep = sleep{Secs := S}
sleepInit(F:sleep, S:float):void =
    set F.Pc = 0
    set F.Secs = S
sleepResume(F:sleep, C:sched):int =
    if (F.Pc = 0):
        set F.Pc = 1
        if (F.Secs >= 0.0, F.Secs < 1000000000000000.0):
            N:int = if (R := Round[F.Secs * 30.0], R >= 1) then R else 1
            set F.Wake = C.Now + N
        else if (F.Secs >= 0.0):
            set F.Wake = -1
        else:
            return 1
    if (F.Wake < 0):
        return 0
    if (C.Now >= F.Wake):
        return 1
    if (C.Next < 0):
        set C.Next = F.Wake
    else if (F.Wake < C.Next):
        set C.Next = F.Wake
    0
Sleep(S:float)<suspends><computes>:void = {}
syncMark(A:[]void)<suspends><computes>:void = {}
raceMark(A:[]void)<suspends><computes>:void = {}
rushMark(A:[]void)<suspends><computes>:void = {}
"

def concTops : Except String (List STop) :=
  parsePrelude concPrelude ["sched", "Now", "Next", "sleep", "Pc", "Secs", "Wake", "sleepNew",
    "sleepInit", "sleepResume", "Sleep", "syncMark", "raceMark", "S", "F", "C", "N", "R", "A",
    "Progress", "Roots", "taskBase", "Done", "Result", "waitf", "T", "X", "waitNew", "waitInit", "waitResume",
    "WaitDone", "Await", "spawnMark", "t", "Sch", "Dead", "evrec", "Got", "Next", "Head", "Tail", "Cur", "W", "L", "V",
    "EvAwait", "E", "branchMark", "rushMark", "signalAll", "H", "StickyAwait", "Last", "CancelCur", "Cancelled", "Running", "Root", "CancelReq", "CurTask", "cancelMark"]

/-- The class of the cells of the stack a lazily taken function with
    several values runs its calls from (#246): an item, and the cells
    below it. Added to a program that has such a function. -/
def lazyPrelude : String := "
lazycell(t:type) := class:
    LItem:t
    LNext:?lazycell(t)
"

def lazyTops : Except String (List STop) := parsePrelude lazyPrelude ["lazycell", "LItem", "LNext"]

/-- `subscribable_event(t)` (#210): an event whose `Signal` also calls the
    functions subscribed to it, each `Subscribe` giving a `cancelable` whose
    `Cancel` unsubscribes it. Added, with the concurrency prelude it
    extends, to a program that mentions it. -/
def subPrelude : String := "
cancelable := interface:
    Cancel():void
subscription := class(cancelable):
    var Live:logic = true
    Cancel<override>():void =
        set Live = false
subscribable_event(t:type) := class(event(t)):
    var Handlers:[]tuple(subscription, type{_(:t):void}) = array{}
    Signal<override>(X:t):void =
        if (Head?) then signalAll(Self, X)
        Hs := Handlers
        set Handlers = for (H : Hs, H(0).Live?) { H }
        for (H : Hs, H(0).Live?):
            H(1)(X)
    Subscribe(F:type{_(:t):void}):cancelable =
        S := subscription{}
        set Handlers += array{(S, F)}
        S
"

/-- `subscribable_event()` (#220): one without a value, whose functions take
    none. Added after `subPrelude` to a program that mentions it. -/
def subVoidPrelude : String := "
subev0 := class(event(void)):
    var Handlers:[]tuple(subscription, type{_():void}) = array{}
    Signal<override>(X:void):void =
        if (Head?) then signalAll(Self, X)
        Hs := Handlers
        set Handlers = for (H : Hs, H(0).Live?) { H }
        for (H : Hs, H(0).Live?):
            H(1)()
    Subscribe(F:type{_():void}):cancelable =
        S := subscription{}
        set Handlers += array{(S, F)}
        S
"

def subTops : Except String (List STop) :=
  parsePrelude subPrelude ["subscription", "Live", "Handlers", "Hs", "H", "S", "F", "X", "t", "Head", "signalAll"]

def subVoidTops : Except String (List STop) :=
  parsePrelude subVoidPrelude ["subscription", "Live", "Handlers", "Hs", "H", "S", "F", "X", "Head", "signalAll", "subev0"]

/-- The tag of the lifts of the refining casts in a function (#53, #243):
    a branch lifted from a class's copy of an interface's default, whose
    name ends with the copy's tag (`$in` and the class), has the copy's, so
    that its own casts' lifts are told apart too. -/
def liftTagOf (name : String) : String :=
  if name.startsWith "$refine" then
    match (name.splitOn "$in").getLast? with
    | some c => if (name.splitOn "$in").length > 1 then s!"$in{c}" else ""
    | none => ""
  else ""

/-- Generated bodies use the same source exits, capture storage and naming
    during effect inference and final elaboration. -/
def functionBodyCtx (opts : Options) (ctx : Ctx) (p : Pos) (name : String)
    (tps : List (String × Bool)) (scopeClass : Option String := none) : Except String Ctx := do
  let lifted := opts.castRequests.find? (·.name == name)
  let loopLift := opts.loopRequests.find? fun l => l.name == name || l.extraFns.any
    (fun | .fn _ n .. => n == name | _ => false)
  let resume := opts.loopRequests.findSome? fun l => l.resumes.find? (·.name == name)
  let source := (resume.map (·.sourceContext)).getD
    ((loopLift.map (·.sourceContext)).getD ((lifted.map (·.sourceContext)).getD {}))
  let returnExit := loopLift.bind (·.returnExit)
  let resumeStorage ← ((resume.map (·.storage)).getD []).mapM fun (n, r) => do
    let args ← r.args.mapM fun t => (resolveTy ctx.types p t).run' { env := ctx.types }
    pure (n, { frame := r.frame, name := r.name, args : SourceStorage })
  let locals ← ctx.locals.mapM fun l => do
    let storage ← ((lifted.bind fun r => r.storage.lookup l.name)).mapM fun r => do
      let args ← r.args.mapM fun t => (resolveTy ctx.types p t).run' { env := ctx.types }
      return { frame := r.frame, name := r.name, args : SourceStorage }
    pure { l with storage := storage.orElse fun _ => (resumeStorage.lookup l.name).orElse fun _ => l.storage }
  let selfCls := (name.splitOn ".").headD ""
  return { ctx with
    locals := locals
    resumeStorage
    frameName := name
    frameArgs := tps.map fun (v, c) => Ty.param v c
    inRepeat := source.inRepeat || (resume.map (·.inRepeat)).getD (lifted.any (·.inRepeat))
    inChoice := source.inChoice || (resume.map (·.inChoice)).getD ctx.inChoice
    inParamDefault := source.inParamDefault || ctx.inParamDefault
    inDefer := source.inDefer || ctx.inDefer
    inDefaultCheck := source.inDefaultCheck || ctx.inDefaultCheck
    inArm := source.inArm || ctx.inArm
    inBranch := source.inBranch || ctx.inBranch
    defaults := source.defaults ++ ctx.defaults
    refineExits := (returnExit.map fun r =>
      { ret := some (r.value.map (fun n => (n, r.ty)), r.packet) : Refine.Exits }).getD
        ((lifted.map (·.exits)).getD {})
    inBlock := source.inBlock || name.endsWith ".$block"
    inCtor := source.inCtor || name.endsWith "$init"
    selfClass := scopeClass.orElse fun _ => match name.splitOn "." with
      | [c, _] => some c | _ => none
    selfMethod := match name.splitOn "." with | [_, m] => some m | _ => none
    liftTag := if scopeClass.isSome then s!"$in{selfCls}" else
      (resume.map (·.liftTag)).getD ((loopLift.map (·.liftTag)).getD
        ((lifted.bind (·.liftTag)).getD (liftTagOf name)))
    refineScope := (lifted.map (·.continuationScope)).getD
      (if loopLift.isSome || resume.isSome then s!"$contScope{name.hash}" else "")
    inlineScopes := (resume.map (·.inlineScopes)).getD
      ((loopLift.map (·.inlineScopes)).getD ((lifted.map (·.inlineScopes)).getD [])) }

/-- The interface whose scope a class's copy of its default is elaborated
    in (#53): its `$copyOf:J` effect, which `copyIfaceDefaults` gives it. -/
def copyScope? (effs : List String) : Option String :=
  effs.findSome? fun e => if e.startsWith "$copyOf:" then some (e.drop 8).toString else none

/-- (#53) An interface that gives a parent interface other type arguments
    than its own type parameters (`c2(t) := interface(container([]t))`) and
    a default body for one of that parent's methods (`Get<override>():[]t`):
    a class that reaches it with type arguments that mention its own type
    parameters gets that body as an override of its own, with the
    interface's type parameters substituted by those type arguments
    (`Refine.substTypes`). A dispatch from
    the parent that opens the class's type parameters reaches the class's
    copy, which reads them from its receiver's hidden fields as any override
    does; the interface's own, shared by all its classes, would need them as
    hidden arguments, which such a dispatch cannot pass. The copy is
    elaborated in the interface's scope (`$copyOf:J`, `copyScope?`): the
    names it uses, its parameters and locals, and `(super:)`, mean what they
    do in the interface's own body, whatever members the class adds. Only
    where the copy means what the default does: no class of the chain
    declares the method (the class chain wins over interface defaults) and
    no other interface above the class gives it a body; a `<final>` default
    stays final, its copy exempt (`$copy`). -/
def copyIfaceDefaults (tops : List STop) : List STop :=
  let defs : List (String × Bool × List TParam × List STy × List String × List STop) := tops.filterMap fun
    | .classDef _ n tps _ parents isI fields _ ms => some (n, isI, tps, parents, fields.map (·.1), ms)
    | _ => none
  let defOf (n : String) := defs.find? (·.1 == n)
  let parentName : STy → String := fun | .app q _ => q | .name q => q | _ => ""
  let baseName (m : String) : String :=
    if m.startsWith "(" then ((m.splitOn ":)").getD 1 m) else m
  -- (everything above `n`, by name, with `n`)
  let supersOf (n : String) : List String := Id.run do
    let mut out := [n]
    let mut frontier := [n]
    for _ in [0:defs.length + 1] do
      let next := (frontier.flatMap fun c => ((defOf c).map fun d => d.2.2.2.1.map parentName).getD []).filter
        (!out.contains ·)
      if next.isEmpty then break
      out := out ++ next.eraseDups
      frontier := next.eraseDups
    return out
  let membersOf (n : String) : List String := match defOf n with
    | some (_, _, _, _, fs, ms) => fs ++ ms.filterMap fun | .fn _ m .. => some (baseName m) | _ => none
    | none => []
  let pinned (tps : List TParam) (parents : List STy) : Bool := parents.any fun
    | .app _ as => as.length != tps.length || (as.zip tps).any fun (a, tp) => match a with
      | .name x => x != tp.name
      | _ => true
    | _ => false
  let mentions (names : List String) (b : SExpr) : Bool := Choice.anyE (fun
    | .ident _ n | .decl _ n .. => names.contains n
    | .gen _ n n2 _ => names.contains n || (n2.map names.contains).getD false
    | _ => false) b
  tops.map fun
    | .classDef cp n tps specs parents false fields ovs ms =>
      let chain := (supersOf n).filter fun c => ((defOf c).map (!·.2.1)).getD false
      let chainDeclares (m : String) : Bool := chain.any fun c => (membersOf c).contains m
      -- (the pinned interfaces reached, each with its type parameters as the
      -- class gives them, through the interfaces between)
      let rec reach (fuel : Nat) (q : String) (qa : List STy) (σ : List (String × STy)) :
          List (String × List (String × STy)) :=
        match fuel, defOf q with
        | f + 1, some (_, true, itps, iparents, _, _) =>
          if qa.length != itps.length then [] else
          let σ' := (itps.map (·.name)).zip (qa.map (·.substNames σ))
          (if !itps.isEmpty && pinned itps iparents then [(q, σ')] else []) ++
            iparents.flatMap fun ip => match ip with
              | .app pq pa => reach f pq pa σ'
              | .name pq => reach f pq [] σ'
              | _ => []
        | _, _ => []
      let selfσ := tps.map fun tp => (tp.name, STy.name tp.name)
      let targets := parents.flatMap fun p => match p with
        | .app q qa => reach (defs.length + 1) q qa selfσ
        | .name q => reach (defs.length + 1) q [] selfσ
        | _ => []
      -- (one copy per interface, also one reached along two paths)
      let targets := targets.foldl (fun acc t => if acc.any (·.1 == t.1) then acc else acc ++ [t]) []
      -- (only where the interface's type arguments mention the class's
      -- type parameters, which a dispatch may open: at closed ones, the
      -- interface's own default takes them as hidden arguments, as now)
      let targets := targets.filter fun (_, σ) =>
        σ.any fun (_, ty) => STy.mentionsAny (tps.map (·.name)) ty
      let extra : List STop := targets.flatMap fun (j, σ) =>
        (((defOf j).map (·.2.2.2.2.2)).getD []).filterMap fun
          | .fn mp m ps mtps effs ret body =>
            -- (every interface that declares the method, above the class or
            -- above any class below it, is `j` or above it: the copy, a
            -- method of the class chain, takes no other interface's slot or
            -- default, which the chain would otherwise win over)
            let below := defs.filterMap fun d => if !d.2.1 && (supersOf d.1).contains n then some d.1 else none
            let jUp := supersOf j
            let others := (below.flatMap supersOf).eraseDups.filter fun i =>
              ((defOf i).map (·.2.1)).getD false && !jUp.contains i && (membersOf i).contains (baseName m)
            if effs.contains "override" && !effs.contains "$abstract" &&
                !m.startsWith "(" && !chainDeclares (baseName m) && others.isEmpty &&
                !mtps.any (fun tp => tps.any (·.name == tp.name)) &&
                -- (nor a type parameter the substitution changes as a name in
                -- an expression, which `Refine.substTypes` leaves: a cast's `c2(t)`)
                !mentions ((σ.filter fun (x, y) => match y with | .name y' => x != y' | _ => true).map (·.1)) body then
              let ps' : List SParam := ps.map fun sp =>
                ({ sp with ty := sp.ty.substNames σ, «default» := sp.default.map (Refine.substTypes σ) } : SParam)
              -- (`$copy`: its `<final>`, if any, is the interface's, which it
              -- is, not overrides; `$copyOf`: elaborated in `j`'s scope, so its
              -- names, `(super:)` included, resolve as in the interface's own)
              some (.fn mp m ps' mtps (effs ++ ["$copy", s!"$copyOf:{j}"]) (ret.substNames σ) (Refine.substTypes σ body))
            else none
          | _ => none
      .classDef cp n tps specs parents false fields ovs (ms ++ extra)
    | t => t

/-- An error of the lowering in function `name` (#156): with the position of
    its definition among `tops`. -/
def inFnMsg (tops : List STop) (name msg : String) : String :=
  let pos := tops.findSome? fun
    | .fn q m .. => if m == name then some q else none
    | .classDef _ c _ _ _ _ _ _ ms => ms.findSome? fun
      | .fn q m .. => if s!"{c}.{m}" == name then some q else none
      | _ => none
    | _ => none
  match pos with
  | some q => s!"{q.show}: in {name}: {msg}"
  | none => s!"in {name}: {msg}"

/-- The type an opened override's result cell holds (#251, #209), in the
    override's own type variables. A caller dispatching from a class above
    it with fewer Verse Core type arguments (a dispatch that opens them)
    passes a cell of the method's result as that class declares it, at the
    dispatch's refinement, and a cell's type is invariant. So: the
    override's own result when such a declaration gives it (the calls that
    worked before go on working); else the result the method's first
    declaration gives at the override's class's type arguments, as
    `sameSigIn` relates the two, which the frame writes its narrower
    (covariant) result to by subsumption; else (the first declarations, one
    per root, #70, disagree, or its own is not below theirs in Verse Core)
    its own. A qualified implementation `(q:)M` has the roots above `q`. -/
def declaredLevels (env : TyEnv) (allS : List Sig) (s : Sig) : VTy × List VTy :=
  let genv : TyEnv := { env with tvars := s.tparams.map fun (v, k) => (v, Ty.param v k) }
  let own := s.ret.toVTy genv
  let c := (s.name.splitOn ".").headD ""
  let m0 := (s.name.drop (c.length + 1)).toString
  let (m, qual) : String × Option String :=
    if m0.startsWith "(" then match (m0.drop 1).toString.splitOn ":)" with
      | [q, m'] => (m', some q)
      | _ => (m0, none)
    else (m0, none)
  let sigAt (r : String) : Option Sig := allS.find? (·.name == s!"{r}.{m}")
  let nps (r : String) : Nat := ((env.sparams.lookup r).getD []).length
  let cps := ((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k
  let sOwn := s.tparams.drop (nps c)
  -- (the declaration's result as an instance of `c` sees it: its own type
  -- parameters renamed apart, then its class's at their arguments in `c`,
  -- then its own as the override's, by position)
  let atC (r : String) (rs : Sig) : Option VTy :=
    let rOwn := rs.tparams.drop (nps r)
    if rOwn.length != sOwn.length then none
    else
      let apart := rOwn.zipIdx.map fun ((x, k), i) => (x, Ty.param s!"$o{i}" k)
      let back := sOwn.zipIdx.map fun ((x, k), i) => (s!"$o{i}", Ty.param x k)
      let cls := (((env.sparams.lookup r).getD []).map (·.1)).zip (env.upArgs c cps r)
      some (((rs.ret.subst apart).subst cls).subst back |>.toVTy genv)
  -- (the classes above `c` on its slot of the method: for a qualified
  -- implementation, those at or above `q`, or between it and `c`)
  let onSlot (r : String) : Bool := match qual with
    | some q => (env.supers q).contains r || env.isSub r q
    | none => true
  let declares (r : String) : Bool := (sigAt r).isSome && onSlot r
  let core (d : String) : Nat :=
    (env.coreArgs d (((env.sparams.lookup d).getD []).map fun (v, k) => Ty.param v k)).length
  let opening := ((env.supers c).drop 1).filter fun r => declares r && core r < core c
  let decls := (env.rootsOf declares (qual.getD c)).map fun r => (sigAt r).bind (atC r)
  let primary : VTy :=
    if opening.any fun r => (sigAt r).bind (atC r) == some own then own else
    match decls with
    | some d :: rest => if rest.all (· == some d) && own.sub d then d else own
    | _ => own
  -- (the other results a caller may expect, from a class it dispatches
  -- from or a first declaration, that a cell of the primary type cannot
  -- serve through a cast, #337: other type arguments, or classes neither
  -- above nor below; each gets a cell of its own, #209)
  let narrowable (d p : VTy) : Bool := match d, p with
    | .ref ud ad, .ref up ap => ad == ap && (ud.all up.contains || up.all ud.contains)
    | _, _ => d == p
  let cands := (opening.filterMap fun r => (sigAt r).bind (atC r)) ++ decls.filterMap id
  let extras := cands.foldl (fun acc d =>
    if d != primary && own.sub d && !narrowable d primary && !acc.contains d then acc ++ [d] else acc) []
  (primary, extras)

/-- The type an opened override's (primary) result cell holds: `declaredLevels`'
    first. -/
def declaredRes (env : TyEnv) (allS : List Sig) (s : Sig) : VTy := (declaredLevels env allS s).1

/-- (#394) `low` with no frames forced open, else again with each frame
    class a call opened (`Suspend.openedTag?`), until none is missing: an
    implementation's frame is made as an opened override's only when a call
    needs it, so programs that do not are lowered as before. -/
def lowerOpening {α : Type} (low : List Nat → Except String α) : Except String α := Id.run do
  let mut forced : List Nat := []
  let mut res := low forced
  for _ in [0:256] do
    match res with
    | .error msg => match Suspend.openedTag? msg with
      | some t =>
        if forced.contains t then return res
        forced := t :: forced
        res := low forced
      | none => return res
    | .ok _ => return res
  return res

/-- The concurrency lowering (#156), at the end of `elabProgramCore`: each
    `<suspends>` function becomes a frame class and its resume, cancel and
    arm functions (`Suspend.lower`), after spawned dispatches are lifted
    (#173); then the task roots (generic ones at their function's type
    arguments, #244), branch wrappers, the scheduler's
    list and, for a suspends `Main`, `$Run` and `$Start`. Gives the
    functions, their slot types and signatures, the class table, the frame
    classes and their pins, and `Main`'s call. (A function of its own, so that `elabProgramCore` stays within
    Lean's elaboration limits.) -/
def lowerConcurrency (env : TyEnv) (sigs gsigs : Array Sig) (mainSig : Sig) (fsigs0 : List (List VTy × VTy))
    (protos : HeapTy) (pins : List (List (Option VTy))) (inFn : String → String → String)
    (fns0 : Array Fn) (slotTys0 : Array (List VTy)) (fsigsIn : List (List VTy × VTy)) (classTable0 : List (List VTy))
    (forced : List Nat := []) (frameInfo : Array FrameRefs.Info := #[]) :
    Except String (Array Fn × Array (List VTy) × List (List VTy × VTy) × List (List VTy) × Array (List VTy) × Expr ×
      List (List (Option VTy)) × List Value) := do
  let mut fns := fns0
  let mut slotTys := slotTys0
  let mut fsigs := fsigsIn
  let mut classTable := classTable0
  let mut frameClasses : Array (List VTy) := #[]
  -- (#244: the pins of the frame classes, in their order: a generic root's
  -- and a branch wrapper's are on all of their type arguments, so that the
  -- scheduler's dispatch opens them)
  let mut framePins : Array (List (Option VTy)) := #[]
  -- (#362: each frame's index of its root's waiting frame, a root's only)
  let mut topIdx : Array Nat := #[]
  let mut extraSigs : Array (List VTy × VTy) := #[]
  let mut mainCall : Expr := .call mainSig.idx []
  let allS := sigs.toList ++ gsigs.toList
  let idxOf (n : String) : Nat := ((allS.find? (·.name == n)).map (·.idx)).getD 0
  let sleepIdx := idxOf "$Sleep"
  let waitIdx := idxOf "$WaitDone"
  let syncMark := idxOf "$syncMark"
  let raceMark := idxOf "$raceMark"
  let rushMark := idxOf "$rushMark"
  let spawnMark := idxOf "$spawnMark"
  let branchMark := idxOf "$branchMark"
  let isMark (f : Nat) : Bool := f == syncMark || f == raceMark || f == rushMark
  let leaves := ["$Sleep", "$WaitDone", "$syncMark", "$raceMark", "$rushMark", "$spawnMark", "$branchMark",
    "$cancelMark"]
  let sigOf (f : Nat) : Option Sig := allS.find? (·.idx == f)
  -- each `spawn` of a method with several implementations (#173): its
  -- dispatch chain becomes a suspends function `$dispatchK` of the slots
  -- it uses (the receiver, the arguments, and the slots its tests bind the
  -- narrowed receiver to, which start as the caller's), which the spawn
  -- calls, so that a spawned dispatch at the caller's type parameters is
  -- a spawn of a call, a root at them (#244), not a reason to copy the
  -- caller per type (#174, #209)
  let dispBase := fns.size
  let mut lifted : Array (Expr × List Nat × Nat) := #[]
  let mut liftedIn : Array Nat := #[]
  for gi in List.range dispBase do
    let n0 := lifted.size
    -- (the slot holding each of its type parameters' values, in their
    -- order: its hidden parameters, then the slots its receiver's fill)
    let witnesses : List Nat := match sigOf gi with
      | some sg =>
        let dictTps := sg.tparams.filter (fun (v, _) => !sg.selfTps.contains v) ++
          sg.tparams.filter (fun (v, _) => sg.selfTps.contains v)
        sg.tparams.filterMap fun (v, _) => (dictTps.findIdx? (·.1 == v)).map (fns[gi]!.arity - sg.ndicts + ·)
      | none => []
    let (body, acc) := (Suspend.liftChains spawnMark dispBase witnesses fns[gi]!.body).run lifted
    -- (every spawn is now of a call, which `spawnSites` finds: its task's
    -- root, generic or not, needs no copy of the function per type, #209;
    -- `elabSpawn` makes only calls and dispatch chains)
    if ((Suspend.callsOf body).filter (·.1 == spawnMark)).length != (Suspend.spawnSites spawnMark body).length then
      throw (inFn fns[gi]!.name "internal error: a spawn of neither a call nor a dispatch chain")
    if acc.size > n0 then
      fns := fns.set! gi { fns[gi]! with body }
      lifted := acc
      liftedIn := liftedIn ++ (List.replicate (acc.size - n0) gi).toArray
  let mut disps : List (Nat × String × Nat) := []
  let mut dispSigs : Array (List VTy × VTy) := #[]
  for ((ch, ops, t), k) in lifted.toList.zipIdx do
    let gi := liftedIn[k]!
    let Γ := slotTys[gi]!
    let tys := ops.map fun o => (Γ[o]?).getD .int
    let ρ ← match Γ[t]? with
      | some (.ref _ [ρ]) => pure ρ
      | _ => throw s!"internal error: lowering {fns[gi]!.name}: a spawn's task"
    fns := fns.push { name := s!"$dispatch{k}", arity := ops.length, nslots := ops.length, decides := false,
                      writes := true, body := Suspend.renumber (fun j => (ops.idxOf? j).getD 0) ch }
    slotTys := slotTys.push tys
    dispSigs := dispSigs.push (tys, ρ)
    -- (generic in the caller's type parameters, whose witnesses it takes
    -- last: its frame then has them, and the spawn is a root at the
    -- caller's type arguments, #244, #209)
    let ntpK := ((sigOf gi).map (·.tparams.length)).getD 0
    disps := disps ++ [(dispBase + k, s!"$dispatch{k}", ntpK)]
  let fsigs0 := fsigs0 ++ dispSigs.toList
  fsigs := fsigs ++ dispSigs.toList
  let user := (allS.filter fun s => s.suspends && !leaves.contains s.name).map
    (fun s => (s.idx, s.name, s.tparams.length)) ++ disps
  let tagBase := env.classes.length
  let schedTag := env.tagOf "$sched"
  let schedTy : VTy := .ref [schedTag] []
  let fieldIdx (c f : String) : Nat := ((env.fields c).findIdx? (·.1 == f)).getD 0
  let Sorig : Sigs := { fns := fsigs0, classes := classTable, protos, pins }
  -- each `spawn` (#156) gets a root: a function `$spawnK(T, args…)` that
  -- runs the spawned call and fills the task `T`
  let mut roots : Array (Nat × String × Nat) := #[]
  -- (each spawn's root's callee's class, when the callee reads type
  -- arguments from its receiver, #209)
  let mut rootSelf : Array (Option String) := #[]
  let mut spawnOf : Array (List Nat) := #[]   -- each user function's spawns' root numbers
  let nFns0 := fns.size
  -- (immediate functions may spawn too: their spawns start the task on
  -- the scheduler, which is its class's prototype, a literal)
  -- (a generic one's spawns are roots at its type arguments, as a generic
  -- suspends function's are, #244: so no function is copied per type, #174)
  let imm := (allS.filter fun s => !s.suspends && !s.isConst &&
    !(Suspend.spawnSites spawnMark fns[s.idx]!.body).isEmpty).map fun s => (s.idx, s.name, s.tparams.length)
  let mut immSpawns : Array (Nat × List Nat) := #[]
  for (gi, gname, ntpC) in user ++ imm do
    let fn := fns[gi]!
    let Γ := slotTys[gi]!
    let mut mine : List Nat := []
    for (h, hs, t) in Suspend.spawnSites spawnMark fn.body do
      let some ttyT := Γ[t]? | throw s!"internal error: lowering {gname}: a spawn's task"
      let mut atys : Array VTy := #[]
      -- (the callee's type arguments, from its witnesses: the last
      -- arguments, one per type parameter but those a method reads from its
      -- receiver, #209)
      let tpsH := ((sigOf h).map (·.tparams)).getD []
      let selfH := ((sigOf h).map (·.selfTps)).getD []
      let witIdx := (List.range tpsH.length).filter fun i => !selfH.contains ((tpsH[i]?.map (·.1)).getD "")
      let wit := (hs.drop (hs.length - witIdx.length)).map fun w => tc Sorig Γ (fsigs0[gi]!).2 w none
      -- (and those it reads from its receiver, which no witness gives: the
      -- receiver's type matched against its receiver parameter's)
      let selfIdx := (List.range tpsH.length).filter (!witIdx.contains ·)
      let recvB : List (Nat × VTy) := if selfIdx.isEmpty then [] else
        match ((fsigs0[h]?).bind (·.1.head?)), (hs.head?.bind fun r => tc Sorig Γ (fsigs0[gi]!).2 r none) with
        | some p0, some τr => VTy.bindVars p0 τr []
        | _, _ => []
      let θh : Nat → VTy := fun i => match (witIdx.idxOf? i).bind (wit[·]?) with
        | some (some τ) => τ
        | _ => (recvB.lookup i).getD (.var i)
      -- (whether a type mentions a type parameter the callee reads from its
      -- receiver that the receiver's type does not give: not expected, as
      -- those are among its class's type arguments, which a receiver of a
      -- reference type repeats; the refusal below stays as a message)
      let mentionsSelf (τ : VTy) : Bool :=
        (τ.subst fun i => if selfIdx.contains i && (recvB.lookup i).isNone then .var 0 else VTy.void).mentionsVar
      -- (and then its class, whose hidden fields its root's slots of those
      -- types start as)
      rootSelf := rootSelf.push (if selfH.isEmpty then none
        else some (((((sigOf h).map (·.name)).getD "").splitOn ".").headD ""))
      for (e, i) in hs.zipIdx do
        match tc Sorig Γ (fsigs0[gi]!).2 e none with
        -- (types that mention the function's type parameters make the root
        -- generic, at the function's type arguments, which the scheduler's
        -- dispatch opens, #244)
        | some τ => atys := atys.push τ
        | none =>
          -- (`array{}` or `false` has no type of its own: the callee's
          -- parameter type at its type arguments, which its witnesses give)
          let pt0 := ((fsigs0[h]?).bind (·.1[i]?)).getD (.var 0)
          let pt := pt0.subst θh
          if !selfH.isEmpty && pt.mentionsVar && mentionsSelf pt0 then
            throw (inFn gname s!"an argument of a spawned call of {((sigOf h).map (·.name)).getD "a method"}, a method that reads type arguments from its receiver, must have a type of its own where its parameter's type mentions them (an empty array or `false` has none): pass it through a variable of its type (#209)")
          if pt.mentionsVar && wit.any (·.isNone) then
            throw (inFn gname "the arguments of a spawned call of a generic function must have types of their own (#156)")
          atys := atys.push pt
      let k := roots.size
      let n := hs.length
      let body : Expr := .seq
        (.heap (.set (fieldIdx "task" "$Result")) [.local 0, .prim .mkSome [.call h ((List.range n).map (fun i => Expr.local (i + 1)))]])
        (.seq (.heap (.set (fieldIdx "task" "$Done")) [.local 0, .lit (.logic true)]) (.lit .void))
      let Γk := ttyT :: atys.toList
      fns := fns.push { name := s!"$spawn{k}", arity := n + 1, nslots := n + 1, decides := false,
                        writes := true, body }
      slotTys := slotTys.push Γk
      roots := roots.push (nFns0 + k, s!"$spawn{k}", if Γk.any (·.mentionsVar) then ntpC else 0)
      mine := mine ++ [k]
    if imm.any (·.1 == gi) then immSpawns := immSpawns.push (gi, mine)
    else spawnOf := spawnOf.push mine
  let fsigs0 := fsigs0 ++ roots.toList.map fun (ri, _, _) => (slotTys[ri]!, VTy.void)
  fsigs := fsigs ++ roots.toList.map fun (ri, _, _) => (slotTys[ri]!, VTy.void)
  let lows := user ++ roots.toList
  -- Spawn argument inference above still sees the original source call
  -- signatures. From here onward generated refining calls carry typed
  -- ancestor references; current-frame placeholders are resolved by lower.
  let sourceFrames ← SourceFrames.prepare
    (fun name => (lows.findIdx? (·.2.1 == name)).map (tagBase + ·)) fns slotTys fsigs0 frameInfo
  fns := sourceFrames.fns
  slotTys := sourceFrames.slots
  fsigs := sourceFrames.sigs
  let fsigs0 := sourceFrames.sigs
  let nFns := fns.size
  -- (#362: a root records the waiting frame to resume first, and the
  -- scheduler the one a resumption found, in fields of this type, after
  -- the scheduler's own)
  let frameAny : VTy := .ref ((List.range lows.length).map (tagBase + ·)) []
  -- (none recorded is the scheduler, as a callee's frame field starts: no
  -- option to allocate at each record)
  let parTy : VTy := .ref ((List.range lows.length).map (tagBase + ·) ++ [schedTag]) []
  let leafF := (classTable[schedTag]?.map (·.length)).getD 0
  let leafDepthF := leafF + 1
  -- (#362) whether chains of waiting frames can get deep: a suspends
  -- function calls itself, directly or through others, or a chain of calls
  -- has more than `leafDepthMin` of them. Only then does the scheduler
  -- resume a root's waiting frame directly, through a dispatch; resuming
  -- a short chain from its root costs no more, and the program is then
  -- compiled as before (its frames not marked done, nothing recorded)
  let leafDepthMin : Nat := 4
  let callsIn : Array (List Nat) := lows.toArray.map fun (gi, _, _) =>
    ((Suspend.callsOf fns[gi]!.body).filterMap fun (f, _) => lows.findIdx? (·.1 == f)).eraseDups
  let leafy : Bool := Id.run do
    -- (the most functions a chain from each has, until nothing grows: still
    -- growing after as many rounds as functions, a cycle)
    let mut d : Array Nat := Array.replicate lows.length 1
    let mut grew := false
    for _ in [0:lows.length + 1] do
      grew := false
      for j in [0:lows.length] do
        let m := ((callsIn[j]?.getD []).map fun i => d[i]?.getD 0).foldl max 0
        if m + 1 > d[j]! then
          d := d.set! j (m + 1)
          grew := true
      if !grew then break
    return grew || d.any (· > leafDepthMin)
  let isS : Nat → Bool := fun f => f == sleepIdx || f == waitIdx || isMark f || lows.any (·.1 == f)
  -- each one's body (initialisations stripped), suspension points and arms
  let mut parts : Array (List Expr × Expr × Nat × Nat) := #[]
  for (gi, gname, _) in lows do
    let fn := fns[gi]!
    let some (ds, b) := Suspend.stripInits (fn.nslots - fn.arity) fn.body
      | throw s!"internal error: lowering {gname}: unexpected initialisations"
    parts := parts.push (ds, b, Suspend.countSusp (fun f => isS f || f == branchMark) (fun _ => false) false (· == spawnMark) b +
        Suspend.countArms (· == rushMark) b,
      Suspend.countArms (fun f => isMark f || f == branchMark) b)
  let frameTy (j : Nat) : VTy :=
    .ref [tagBase + j] ((List.range lows[j]!.2.2).map VTy.var)
  let sourceBase (name : String) : Option Nat := do
    let j ← lows.findIdx? (·.2.1 == name)
    let (_, _, sites, arms) := parts[j]!
    return Suspend.slotBaseOf sites arms
  -- These layouts expose the original slot prefix to ANF type inference.
  -- Lowering appends its transient slots without moving that prefix.
  let sourceClasses := lows.zipIdx.map fun ((gi, _, _), j) =>
    let (_, _, sites, arms) := parts[j]!
    List.replicate (Suspend.slotBaseOf sites arms) VTy.void ++ slotTys[gi]!
  let Ssource : Sigs := { fns := fsigs0, classes := classTable ++ sourceClasses, protos, pins }
  for gi in List.range fns.size do
    if lows.any (·.1 == gi) then continue
    let shared ← SourceFrames.aliases sourceFrames gi sourceBase
    let (fn, tys) ← SourceFrames.immediate Ssource fns[gi]! slotTys[gi]! shared
      (sourceFrames.info[gi]?.getD {}).copies
    fns := fns.set! gi fn
    slotTys := slotTys.set! gi tys
  -- the methods called through `Typed.dispatch` (#142) of classes that fix
  -- type arguments (a generic one at or above the receiver's class is
  -- called without the refinement, so it is never one)
  let targets : List Nat := (lows.foldl (fun acc (gi, _, _) => acc ++
    Suspend.dispatchTargets (fun f => user.any fun (h, _, _) => h == f) fns[gi]!.body) []).eraseDups
  -- each one's `new`, `reset`, `cancel` and `result` (fixed indices), then
  -- each one's `arrive`, `resumeOwn`, `cancelOwn` and `newCell`,
  -- each target's receiver-first `take`, each root's trampoline and
  -- `start`, then the arms' functions
  -- (the overrides whose class has type parameters its parent's type
  -- arguments do not give: a dispatch may open their frames' type
  -- arguments, #251)
  -- (#394: and the implementations whose frames a call opens although they
  -- have none of those, `forced`: one that a class below inherits while
  -- fixing one of its class's type arguments to a type that mentions its
  -- own, `c3(t) := class(c1(tuple(char, t)))`, which a dispatch to it opens;
  -- the lowering finds them, and is run again with them, `lowerOpening`)
  let opened (j : Nat) : Bool := match lows[j]? with
    | some (gi, _, _) => ((sigOf gi).map (!·.selfTps.isEmpty)).getD false || forced.contains (tagBase + j)
    | none => false
  -- (the type such an override's result cell holds: its method's declared
  -- result, so that a narrower, covariant, one is called as any other, #209)
  let cellResOf (j : Nat) : VTy := match lows[j]? with
    | some (gi, _, _) => match sigOf gi with
      | some s => if opened j then declaredRes env allS s else (fsigs0[gi]!).2
      | none => (fsigs0[gi]!).2
    | none => .void
  -- (and the other result cells such a frame keeps, for callers that
  -- expect another declared result no cast serves, #209: each with its
  -- `newCell`, in a block after the `own` functions)
  -- (computed once: each lookup and each offset reads the arrays)
  let moreArr : Array (List VTy) := (List.range lows.length).toArray.map fun j => match lows[j]? with
    | some (gi, _, _) => if opened j then ((sigOf gi).map fun s => (declaredLevels env allS s).2).getD [] else []
    | none => []
  let offArr : Array Nat := moreArr.foldl (fun acc m => acc.push (acc.back?.getD 0 + m.length)) #[0]
  let moreOf (j : Nat) : List VTy := moreArr[j]?.getD []
  let moreOff (j : Nat) : Nat := offArr[j]?.getD 0
  let L := lows.length
  -- Only refining lifts borrow task ownership. Ordinary callees still
  -- stop their own roots when they return. A nested lift forwards through
  -- every enclosing lift, including one that starts no roots directly.
  let lifts := lows.filter fun (_, name, _) => defaultBridge name || env.castRequests.any (·.name == name)
  let mut taskLifts := lifts.filterMap fun (gi, _, _) =>
    if Suspend.countSusp (· == branchMark) (fun _ => false) false (· == spawnMark) fns[gi]!.body > 0 ||
        Suspend.countArms (· == rushMark) fns[gi]!.body > 0 then some gi else none
  for _ in List.range lifts.length do
    for (gi, _, _) in lifts do
      if !taskLifts.contains gi && (Suspend.callsOf fns[gi]!.body).any (fun (g, _) => taskLifts.contains g) then
        taskLifts := taskLifts ++ [gi]
  let taskFrames := lows.zipIdx.filterMap fun ((gi, _, _), j) => if taskLifts.contains gi then some j else none
  -- Borrowed helpers can interleave roots with sibling arms. A shared
  -- clock and single-root cleanup merge them in actual source start order.
  let taskClockF : Option Nat := if taskFrames.isEmpty then none else some (leafF + if leafy then 2 else 0)
  let taskStride := if taskClockF.isSome then 4 else 2
  let ownBase := nFns + 4 * L
  let moreBase := ownBase + 4 * L
  let taskBase := moreBase + moreOff L
  let taskIndex (j : Nat) := taskFrames.idxOf? j
  let selfBase := taskBase + taskStride * taskFrames.length
  let trampOf (k : Nat) : Nat := selfBase + targets.length + 2 * k
  -- the scheduler: its class's prototype
  let some schedLit := Suspend.coreDefault Sorig [] 0 schedTy
    | throw "internal error: no prototype for the scheduler"
  -- an immediate function's spawns: start the task now
  for (gi, ks) in immSpawns do
    let fn := fns[gi]!
    let body := Suspend.substSpawns spawnMark (fun i _ hs t =>
      let k := (ks[i]?).getD 0
      .call (trampOf k + 1) [schedLit, .call (nFns + 4 * (user.length + k)) (schedLit :: .local t :: hs)]) fn.body
    fns := fns.set! gi { fn with writes := true, body }
  -- each `branch` (numbered across the functions, in order) gets a
  -- wrapper class `[pc, frame, owner]` and its `tramp`, `start` and `stop`
  let mut branchOf : Array (List Nat) := #[]
  let mut branchHome : Array Nat := #[]
  for (j, part) in (List.range L).zip parts.toList do
    let n := Suspend.countSusp (· == branchMark) (fun _ => false) false (fun _ => false) part.2.1 +
      Suspend.countArms (· == rushMark) part.2.1
    branchOf := branchOf.push ((List.range n).map (· + branchHome.size))
    branchHome := branchHome ++ (List.replicate n j).toArray
  let B := branchHome.size
  -- (`$link(sched, root)`, which adds a root to the scheduler's list,
  -- comes before them)
  let linkIdx := selfBase + targets.length + 2 * roots.size
  let wrapFnBase := linkIdx + 1
  let wrapTag (K : Nat) : Nat := tagBase + L + K
  -- (after the wrappers' classes, the root list's cells', then an empty
  -- class without type parameters: its objects, made at any type arguments,
  -- first fill a generic callee's frame field, #256)
  let nilTag := tagBase + L + B + 1
  -- (then `$cell(t)`, a caller's result cell for an opened override, #251)
  let resCellTag := tagBase + L + B + 2
  -- (a branch's wrapper holds its home's frame, at its type arguments,
  -- which the scheduler's dispatch opens, #244)
  let ntpOfLow (j : Nat) : Nat := ((lows[j]?).map (·.2.2)).getD 0
  -- A borrower keeps its arguments in its own frame, even without type
  -- parameters. Keeping another copy in the caller would require a
  -- recursive default for a caller passing its own source frame.
  let ownArgs (j : Nat) : Bool := ntpOfLow j != 0 ||
    ((lows[j]?).map fun (gi, _, _) => !(sourceFrames.refs[gi]?.getD []).isEmpty).getD false
  let wrapTy (K : Nat) : VTy := .ref [wrapTag K] ((List.range (ntpOfLow (branchHome[K]?.getD 0))).map VTy.var)
  let callee : Nat → Option Suspend.Callee := fun f =>
    if f == sleepIdx then
      some { tag := env.tagOf "$sleep", newFn := idxOf "$sleepNew", initFn := idxOf "$sleepInit",
             resumeFn := idxOf "$sleepResume", cancelFn := none, passFields := [], resField := none }
    else if f == waitIdx then
      some { tag := env.tagOf "$waitf", newFn := idxOf "$waitNew", initFn := idxOf "$waitInit",
             resumeFn := idxOf "$waitResume", cancelFn := none, passFields := [], resField := none }
    else match lows.zipIdx.find? (·.1.1 == f) with
      | some ((gi, _, ntp), j) =>
        let (_, _, sites, arms) := parts[j]!
        -- (a generic one is arrived at through `arrive`, and resumed and
        -- cancelled with its parameters from its frame, as its caller has no
        -- slots of their types, #256)
        some { tag := tagBase + j, newFn := nFns + 4 * j, initFn := nFns + 4 * j + 1,
               arriveFn := some (ownBase + 4 * j),
               resumeFn := if ownArgs j then ownBase + 4 * j + 1 else gi,
               cancelFn := some (if ownArgs j then ownBase + 4 * j + 2 else nFns + 4 * j + 2),
               newCellFn := if opened j then some (ownBase + 4 * j + 3) else none,
               cellRes := if opened j then some (cellResOf j) else none,
               moreCells := (moreOf j).zipIdx.map fun (d, i) => (moreBase + moreOff j + i, d),
               passFields := if ownArgs j then [] else
                 (List.range fns[gi]!.arity).map fun i => Suspend.slotBaseOf sites arms + i,
               resField := some Suspend.resF, generic := ownArgs j, newSched := true,
               resultFn := some (nFns + 4 * j + 3), ntp,
               stopTasksFn := (taskIndex j).map fun i => taskBase + taskStride * i + 1,
               taskOrderFn := if taskClockF.isSome then (taskIndex j).map (fun i => taskBase + taskStride * i + 3) else none,
               selfFns := (targets.idxOf? gi).map fun i =>
                 (ownBase + 4 * j, selfBase + i, ownBase + 4 * j + 1, ownBase + 4 * j + 2) }
      | none => none
  for ((gi, _, _), j) in lows.zipIdx do
    let ps := slotTys[gi]!.take fns[gi]!.arity
    extraSigs := extraSigs.push (schedTy :: ps, frameTy j)
    extraSigs := extraSigs.push (frameTy j :: ps, VTy.void)
    extraSigs := extraSigs.push (frameTy j :: schedTy :: ps, VTy.void)
    extraSigs := extraSigs.push ([frameTy j], (fsigs0[gi]!).2)
  -- each one's `arrive(params…, frame, sched)`, which resets the frame or
  -- makes one and gives it (a plain call, so that its arguments are checked
  -- against its parameters' types), and `resumeOwn(frame, sched)` and
  -- `cancelOwn(frame, sched)`, which pass its parameters from its frame; a
  -- frame field has type `ref [frame, sched] []`, or for a generic one
  -- `ref [frame, $nil] args` (#256); an opened override's `newCell(params…,
  -- cell, sched)` makes a frame, its body built with its `new`'s after the
  -- lowering (another's is a stub, never called), and its `resumeOwn` also
  -- writes its result to its cell when it is done (#251)
  let cellTyOf (j : Nat) : VTy := match lows[j]? with
    | some _ => .ref [resCellTag] [cellResOf j]
    | none => .void
  let stub : Fn := { name := "$unused", arity := 0, nslots := 0, decides := false, writes := false,
                     body := .prim .userErr [] }
  let wideOf (j : Nat) : VTy :=
    if ownArgs j then .ref [tagBase + j, nilTag] ((List.range (ntpOfLow j)).map VTy.var)
    else .ref [tagBase + j, schedTag] []
  let mut ownFns : Array Fn := #[]
  let mut ownTys : Array (List VTy) := #[]
  for ((gi, gname, _), j) in lows.zipIdx do
    let (_, _, sites, arms) := parts[j]!
    let a := fns[gi]!.arity
    let ps := slotTys[gi]!.take a
    let locals := (List.range a).map Expr.local
    let pass := (List.range a).map fun i => Expr.heap (.get (Suspend.slotBaseOf sites arms + i)) [.local 0]
    let arriveBody : Expr := .seq (.ite (.heap (.isTag [tagBase + j]) [.local a]) (.call (nFns + 4 * j + 1) (.local a :: locals))
      (.seq (.assign a (.call (nFns + 4 * j) (.local (a + 1) :: locals))) Suspend.vd)) (.local a)
    ownFns := ownFns ++ #[
      { name := s!"{gname}$arrive", arity := a + 2, nslots := a + 2, decides := false, writes := true,
        body := arriveBody },
      { name := s!"{gname}$resumeOwn", arity := 2, nslots := 2, decides := false, writes := true,
        body := .call gi (.local 0 :: .local 1 :: pass) },
      { name := s!"{gname}$cancelOwn", arity := 2, nslots := 2, decides := false, writes := true,
        body := .call (nFns + 4 * j + 2) (.local 0 :: .local 1 :: pass) }, stub]
    ownTys := ownTys ++ #[ps ++ [wideOf j, schedTy], [frameTy j, schedTy], [frameTy j, schedTy]]
    extraSigs := extraSigs ++ #[(ps ++ [wideOf j, schedTy], wideOf j), ([frameTy j, schedTy], .int),
      ([frameTy j, schedTy], VTy.void)]
    if opened j then
      ownTys := ownTys.push (ps ++ [cellTyOf j, schedTy])
      extraSigs := extraSigs.push (ps ++ [cellTyOf j, schedTy], frameTy j)
    else
      ownTys := ownTys.push []
      extraSigs := extraSigs.push ([], VTy.void)
  -- each opened override's other cells' `newCell(params…, cell, sched)`
  -- (#209), built after the lowering as its first's
  for ((gi, _, _), j) in lows.zipIdx do
    let ps := slotTys[gi]!.take fns[gi]!.arity
    for d in moreOf j do
      ownFns := ownFns.push stub
      ownTys := ownTys.push (ps ++ [.ref [resCellTag] [d], schedTy])
      extraSigs := extraSigs.push (ps ++ [.ref [resCellTag] [d], schedTy], frameTy j)
  -- Sharing lifts expose a stop and optional latest-order query, each with
  -- a wrapper reading parameters from the retained frame like cancelOwn.
  for j in taskFrames do
    let (gi, _, _) := lows[j]!
    let ps := slotTys[gi]!.take fns[gi]!.arity
    extraSigs := extraSigs ++ #[(frameTy j :: schedTy :: ps, VTy.void), ([frameTy j, schedTy], VTy.void)]
    if taskClockF.isSome then
      extraSigs := extraSigs ++ #[(frameTy j :: schedTy :: ps, VTy.int), ([frameTy j, schedTy], VTy.int)]
  -- each target's `take(self, frame)` (#142), whose first parameter is the
  -- receiver: the frame's result (its frame is made, resumed and cancelled
  -- through its `arrive`, `resumeOwn` and `cancelOwn`)
  let mut selfFns : Array Fn := #[]
  let mut selfTys : Array (List VTy) := #[]
  let mut selfSigs : Array (List VTy × VTy) := #[]
  for gi in targets do
    let some j := lows.findIdx? (·.1 == gi) | throw "internal error: a dispatch target"
    let (_, gname, _) := lows[j]!
    let ps := slotTys[gi]!.take fns[gi]!.arity
    let ρ := (fsigs0[gi]!).2
    let take : Fn := { name := s!"{gname}$take", arity := 2, nslots := 2, decides := false, writes := false,
                       body := .ite (.heap (.isTag [tagBase + j]) [.local 1]) (.call (nFns + 4 * j + 3) [.local 1])
                         (.prim .userErr []) }
    selfFns := selfFns.push take
    selfTys := selfTys.push [ps.headD .int, wideOf j]
    selfSigs := selfSigs.push ([ps.headD .int, wideOf j], ρ)
  let rootJ (k : Nat) : Nat := user.length + k
  let rootTags := (List.range roots.size).map (fun k => tagBase + rootJ k) ++ (List.range B).map wrapTag
  let mainJ := (lows.findIdx? (·.1 == mainSig.idx)).getD 0
  let rootAnyTags : List Nat := (tagBase + mainJ) :: rootTags
  let rootAny : VTy := .ref rootAnyTags []
  -- each root's trampoline (frame, sched) and `start(sched, frame)`
  let mut rootSigs : Array (List VTy × VTy) := #[]
  for k in List.range roots.size do
    rootSigs := rootSigs.push ([frameTy (rootJ k), schedTy], .int)
    rootSigs := rootSigs.push ([schedTy, frameTy (rootJ k)], VTy.void)
  -- a task's root: the type of its `Root` field (in every class that has
  -- it), before the frames' defaults are built from the class table (a
  -- task temporary's `Root` starts as `false`, not as a `?int` parameter
  -- the prelude's placeholder type would allow)
  for d in env.classes do
    if let some ri := (env.fields d).findIdx? (·.1 == "$Root") then
      classTable := classTable.set (env.tagOf d) ((classTable[env.tagOf d]!).set ri (.opt rootAny))
  if leafy then classTable := classTable.set schedTag (classTable[schedTag]! ++ [parTy, .int])
  if taskClockF.isSome then classTable := classTable.set schedTag (classTable[schedTag]! ++ [.int])
  let Sinf : Sigs := { fns := fsigs0 ++ extraSigs.toList ++ selfSigs.toList ++ rootSigs.toList, classes := classTable ++ sourceClasses,
                       protos, pins }
  let mut newFns : Array Fn := #[]
  let mut newTys : Array (List VTy) := #[]
  let mut taskFns : Array Fn := #[]
  let mut taskTys : Array (List VTy) := #[]
  let mut armFns : Array Fn := #[]
  let mut armTys : Array (List VTy) := #[]
  let mut armSigs : Array (List VTy × VTy) := #[]
  let armBase := wrapFnBase + 3 * B
  let mut branchFns : Array Fn := #[]
  let mut branchTys : Array (List VTy) := #[]
  -- (each branch's arm resume function, done field, and the passing of its
  -- function's parameters from the frame, for cancelling it)
  let mut branchInfo : Array (Nat × Nat × List Expr) := #[]
  let mut branchSigs : Array (List VTy × VTy) := #[]
  let progressF := fieldIdx "$sched" "$Progress"
  let headF := fieldIdx "$sched" "$Head"
  let tailF := fieldIdx "$sched" "$Tail"
  -- (set when a root ends or is stopped: the list then has cells to drop)
  let deadF := fieldIdx "$sched" "$Dead"
  -- (cancellation: the task's flags and root; the scheduler's request to
  -- cancel the root that just ran)
  let cancelCurF := fieldIdx "$sched" "$CancelCur"
  -- (#253) a root's first run happens inline, in its parent's resumption:
  -- a request to cancel the root that ran (awaiting a cancelled task,
  -- cancelling its own) is then for it, not for the root the scheduler is
  -- resuming; its start function takes it (`$cancelRoot`, whose index is
  -- known only later: a mark, substituted then)
  let cancelRootMark : Nat := 0xFFFFFF
  -- (and `$cancelTaskRoot(sched, task)`, which unwinds a task's root, #270)
  let cancelTaskRootMark : Nat := 0xFFFFFE
  -- (one that ended in that run, `st` 1, is not cancelled after it)
  let takeCancel (root st : Expr) : Expr :=
    .ite (.prim .query [.heap (.get cancelCurF) [.local 0]])
      (.seq (Suspend.seqVoid [.heap (.set cancelCurF) [.local 0, .lit (.logic false)],
        .ite (.prim .eq [st, Suspend.int 1]) Suspend.vd (.seq (.call cancelRootMark [.local 0, root]) Suspend.vd)])
        Suspend.vd) Suspend.vd
  -- (#362) a root's chain resumed from the waiting frame it recorded,
  -- through `$resumeAny` (a mark: its index is known only later), else, or
  -- once that frame is done, from the root itself (`direct`), in slot `st`
  -- (slot `s` the recorded frame's result, `f` whether it waits). The
  -- root then records the frame its resumption found waiting: from the
  -- recorded frame, the one found; from the root, the one found only when
  -- at least `leafDepthMin` waiting frames are above it (nearer, resuming
  -- from the root costs no more than the dispatch to it); else none, which
  -- resumes the whole chain, as each pass did before
  let resumeAnyMark : Nat := 0xFFFFFD
  let forget (sch : Expr) : List Expr := if leafy then [.heap (.set leafDepthF) [sch, Suspend.int (-1)]] else []
  let depth (sch : Expr) : Expr := .heap (.get leafDepthF) [sch]
  let resumeChain (root sch direct : Expr) (topF st s f : Nat) : List Expr :=
    if !leafy then [.assign st direct] else
    let forget (sch : Expr) : Expr := .heap (.set leafDepthF) [sch, Suspend.int (-1)]
    [
    .assign f (Suspend.int 0),
    -- (`$resumeAny(recorded, sched)`: -1 when none is recorded)
    .assign st (.seq (forget sch)
      (.seq (.assign s (.call resumeAnyMark [.heap (.get topF) [root], sch]))
        (.ite (.prim .eq [.local s, Suspend.int 0])
          (.seq (.assign f (Suspend.int 1)) (.local s))
          (.seq (forget sch) direct)))),
    .ite (.prim .eq [.local st, Suspend.int 0])
      (.seq (.heap (.set topF) [root, .ite (.prim .lt [depth sch, Suspend.int 0]) sch
          (.ite (.prim .eq [.local f, Suspend.int 1]) (.heap (.get leafF) [sch])
            (.ite (.prim .le [Suspend.int leafDepthMin, depth sch]) (.heap (.get leafF) [sch]) sch))])
        Suspend.vd) Suspend.vd]
  -- (and after a root's first run, inline in another's resumption, what it
  -- recorded is forgotten: the other's frames record afresh when they wait,
  -- as one that recorded before in this resumption is in an arm of a
  -- `sync`, `race` or `rush`, which records itself or forgets, #362)
  let tDoneF := fieldIdx "task" "$Done"
  let tCancelledF := fieldIdx "task" "$Cancelled"
  let runningF := fieldIdx "task" "$Running"
  let rootF := fieldIdx "task" "$Root"
  let cancelReqF := fieldIdx "task" "$CancelReq"
  -- (#260: the task whose code runs, a dummy one for `Main`'s; a branch's
  -- wrapper records it as its owner, which is running while the branch
  -- runs)
  let curTaskF := fieldIdx "$sched" "$CurTask"
  let ownerF := 2
  let taskBaseTy : VTy := (Ty.struct "$taskBase" []).toVTy env
  for ((gi, gname, _), j) in lows.zipIdx do
    let fn := fns[gi]!
    let Γ := slotTys[gi]!
    let a := fn.arity
    let (ds, b, sites, arms) := parts[j]!
    let ρ := (fsigs0[gi]!).2
    let fnBase := armBase + armFns.size
    let spawns : Array (Nat × Nat) := ((spawnOf[j]?).getD []).toArray.map fun k =>
      (nFns + 4 * rootJ k, trampOf k + 1)
    let branches : Array (Nat × Nat × Nat) := ((branchOf[j]?).getD []).toArray.map fun K =>
      (wrapFnBase + 3 * K + 1, wrapFnBase + 3 * K + 2, wrapTag K)
    let isRoot := j ≥ user.length || (mainSig.suspends && gi == mainSig.idx)
    let shared ← SourceFrames.aliases sourceFrames gi sourceBase
    let low ← (Suspend.lower Sinf callee syncMark raceMark rushMark spawnMark spawns branchMark branches a Γ ρ (frameTy j)
      schedTag nilTag resCellTag fnBase b leafF leafDepthF isRoot leafy resumeAnyMark leafDepthMin parTy shared
      (sourceFrames.info[gi]?.getD {}).copies (taskLifts.contains gi) taskClockF).mapError fun e => inFn gname e
    -- its branches' wrappers: `tramp(w, sched)` resumes the arm (with the
    -- function's parameters from its frame) unless the function stopped
    -- it; `start(sched, frame)` makes the wrapper, registers it and runs
    -- it once; `stop(w)` marks it done
    let (_, _, sitesJ, armsJ) := parts[j]!
    for (K, (armRes, doneA, runNow)) in ((branchOf[j]?).getD []).zip low.branchArms do
      let fr : Expr := .heap (.get 1) [.local 0]
      let pass := (List.range a).map fun i => Expr.heap (.get (Suspend.slotBaseOf sitesJ armsJ + i)) [fr]
      branchInfo := branchInfo.push (armRes, doneA, pass)
      -- (a `rush` loser that runs `return` after the `rush` ended has
      -- unwound itself and ends there: it is marked so, and not stopped
      -- again when the function exits, #181)
      -- (#362: resumed from the waiting frame its arm recorded, as a root;
      -- the arms' records are the frame's last fields)
      let armTopIdx := low.fields.length - armsJ + (armRes - fnBase) / 2
      let resumeArm : List Expr := resumeChain fr (.local 1) (.call armRes (fr :: .local 1 :: pass)) armTopIdx 2 6 7 ++
        (if leafy then [.ite (.prim .eq [.local 2, Suspend.int 0]) Suspend.vd
          (.seq (.heap (.set armTopIdx) [fr, .local 1]) Suspend.vd)] else [])
      let tramp : Expr := .seq (.ite (.prim .eq [.heap (.get doneA) [fr], Suspend.int 0])
          (.seq (Suspend.seqVoid (resumeArm ++ [
            .ite (.prim .eq [.local 2, Suspend.int 1]) (.seq (.heap (.set doneA) [fr, Suspend.int 1]) Suspend.vd) Suspend.vd,
            .ite (.prim .eq [.local 2, Suspend.int 2])
              (.seq (Suspend.seqVoid [.heap (.set doneA) [fr, Suspend.int 2], .assign 2 (Suspend.int 1)]) Suspend.vd)
              Suspend.vd]))
            Suspend.vd)
          (.seq (.assign 2 (Suspend.int 1)) Suspend.vd)) (.local 2)
      -- (its owner task is running while it runs, #260: a cancel of it
      -- from here is taken after the run, unless it was running already,
      -- its own code having started the branch, whose trampoline takes it)
      let owned : Expr := Suspend.seqVoid [
        .assign 4 (.heap (.get runningF) [.local 3]),
        .heap (.set runningF) [.local 3, .lit (.logic true)],
        .heap (.set curTaskF) [.local 1, .local 3],
        .assign 2 tramp,
        .heap (.set curTaskF) [.local 1, .local 5],
        .heap (.set runningF) [.local 3, .local 4],
        .ite (.prim .eq [.local 4, .lit (.logic false)])
          (.seq (.ite (.prim .query [.heap (.get cancelReqF) [.local 3]])
            (.seq (Suspend.seqVoid [.heap (.set cancelReqF) [.local 3, .lit (.logic false)],
              .call cancelTaskRootMark [.local 1, .local 3]])
              Suspend.vd) Suspend.vd) Suspend.vd) Suspend.vd] |> fun e => Expr.seq e (.local 2)
      branchFns := branchFns.push { name := s!"$branch{K}$tramp", arity := 2, nslots := if leafy then 8 else 6,
                                    decides := false, writes := true, body := initPrefixE 2 ([Suspend.int 0,
                                      .heap (.get ownerF) [.local 0], .lit (.logic false),
                                      .heap (.get curTaskF) [.local 1]] ++
                                      (if leafy then [Suspend.int 0, Suspend.int 0] else [])) owned }
      branchTys := branchTys.push ([wrapTy K, schedTy, .int, taskBaseTy, .logic, taskBaseTy] ++
        (if leafy then [.int, .int] else []))
      branchSigs := branchSigs.push ([wrapTy K, schedTy], .int)
      -- (a `rush` loser's wrapper only registers it: it already started)
      let register : Expr := .call linkIdx [.local 0, .local 2]
      let start : Expr := .seq (Suspend.seqVoid (if !runNow then [register] else [register,
        .assign 4 (.heap (.get cancelCurF) [.local 0]),
        .heap (.set cancelCurF) [.local 0, .lit (.logic false)]] ++
        -- (what its run recorded is forgotten, as after a root's, #362)
        [.assign 3 (.call (wrapFnBase + 3 * K) [.local 2, .local 0])] ++ forget (.local 0) ++ [
        takeCancel (.local 2) (.local 3),
        .heap (.set cancelCurF) [.local 0, .local 4],
        .ite (.prim .eq [.local 3, Suspend.int 1])
          (.seq (Suspend.seqVoid [.heap (.set Suspend.pcF) [.local 2, Suspend.int (-1)],
            .heap (.set progressF) [.local 0, .lit (.logic true)], .heap (.set deadF) [.local 0, .lit (.logic true)]])
            Suspend.vd) Suspend.vd])) (.local 2)
      let startFn : Fn := { name := s!"$branch{K}$start", arity := 2, nslots := 5, decides := false, writes := true,
                            body := initPrefixE 2 [.heap (.new (wrapTag K)) [Suspend.int 0, .local 1,
                              .heap (.get curTaskF) [.local 0]], Suspend.int 0,
                              .lit (.logic false)] start }
      branchFns := branchFns.push startFn
      branchTys := branchTys.push [schedTy, frameTy j, wrapTy K, .int, .logic]
      branchSigs := branchSigs.push ([schedTy, frameTy j], wrapTy K)
      let stopFn : Fn := { name := s!"$branch{K}$stop", arity := 2, nslots := 2, decides := false, writes := true,
                           body := Suspend.seqVoid [.heap (.set Suspend.pcF) [.local 0, Suspend.int (-1)],
                             .heap (.set deadF) [.local 1, .lit (.logic true)]] }
      branchFns := branchFns.push stopFn
      branchTys := branchTys.push [wrapTy K, schedTy]
      branchSigs := branchSigs.push ([wrapTy K, schedTy], VTy.void)
    let ps := Γ.take a
    -- (an opened override's own type parameters have no parameters of their
    -- own: their values are the receiver's hidden fields, as in its body,
    -- #209, #251; the receiver is the first of the function's parameters,
    -- which come last)
    let selfCls := (gname.splitOn ".").headD ""
    -- (a spawn's root whose callee reads type arguments from its receiver,
    -- its second parameter, after the task, likewise: a field of the
    -- receiver's class, hidden or not, or a part of one through tuples,
    -- whose type at the receiver's type arguments is the variable (the
    -- callee's class may hold only a composite of it, `mid(tuple(u, v),
    -- int)`'s `a`); a generic root's other variables have witnesses among
    -- its arguments)
    let rootVarD (params : List VTy) (i : Nat) : Option Expr := do
      if gi < nFns0 then none
      let _ ← (rootSelf[gi - nFns0]?).join
      let ri := params.length - a + 1
      let recv@(.ref _ _) ← params[ri]? | none
      Suspend.partOfType classTable (.var i) (.local ri) recv 16
    let varD (params : List VTy) (i : Nat) : Option Expr := (do
      let s ← sigOf gi
      let (v, _) ← s.tparams[i]?
      if !s.selfTps.contains v then none
      let k ← env.witnessField? selfCls v
      some (.heap (.get k) [.local (params.length - a)])) <|> rootVarD params i
    let coreDflt (params : List VTy) (τ : VTy) : Except String Expr :=
      match Suspend.coreDefault Sinf params 0 τ (varD params) with
      | some d => pure d
      | none => throw s!"internal error: lowering {gname}: no initial value for a slot of type {repr τ}"
    -- (a slot holding a generic callee's frame, of type `ref [frame, $nil]
    -- args`, starts as the frame's field for it in a function whose first
    -- parameter is the frame, `ownFrame`, and as an empty object elsewhere:
    -- no allocation at each resumption, #256; the value only types the slot,
    -- which every path assigns before reading, so the first field of that
    -- type does, even when it is another call site's)
    let dflt (params : List VTy) (τ : VTy) (ownFrame : Bool := false) : Except String Expr :=
      match τ with
      -- (a result cell, #251: made with a value of its type)
      | .ref [t] [x] =>
        if t == resCellTag then do pure (.heap (.new resCellTag) [← coreDflt params x]) else coreDflt params τ
      | .ref ts _ =>
        if !ts.contains nilTag then coreDflt params τ
        else match (if ownFrame then low.fields.idxOf? τ else none) with
          | some f => pure (.heap (.get f) [.local 0])
          | none => pure (.heap (.new nilTag) [])
      | _ => coreDflt params τ
    -- the frame's slots after the parameters: the function's own, then the
    -- pass's temporaries (and, where frames are resumed directly, the arms'
    -- records, #362, each starting as none, the scheduler)
    let tempTys := (low.fields.drop (2 + sites + 2 * arms + a + (fn.nslots - a)))
    -- each function keeps its parameters and the transient slots it uses
    let resumeLike (name : String) (lf : Suspend.LFn) : Except String Fn := do
      let inits ← (lf.slots.drop (a + 2)).mapM (dflt (lf.slots.take (a + 2)) · true)
      return { name, arity := a + 2, nslots := lf.slots.length, decides := false, writes := true,
               body := initPrefixE (a + 2) inits lf.body }
    fns := fns.set! gi (← resumeLike gname low.body)
    slotTys := slotTys.set! gi low.body.slots
    fsigs := fsigs.set gi (frameTy j :: schedTy :: ps, .int)
    -- (an opened override's frame has its result cell last, and pins on all
    -- of its type arguments, so that a dispatch opens them, #251)
    let cellF := low.fields.length
    let more := moreOf j
    -- (a root's last field, #362: its waiting frame to resume first)
    frameClasses := frameClasses.push (low.fields ++
      (if opened j then cellTyOf j :: more.map fun d => .ref [resCellTag] [d] else []) ++
      (if leafy && isRoot then [parTy] else []))
    topIdx := topIdx.push (low.fields.length + (if opened j then 1 + more.length else 0))
    -- (#362: every generic frame's where the scheduler resumes any waiting
    -- frame, through a dispatch that opens its type arguments, `$resumeAny`)
    framePins := framePins.push (if leafy || j ≥ user.length || opened j then List.replicate (ntpOfLow j) none else [])
    -- `g$new(sched, params…)`: the frame, with the arguments and initial
    -- values (a non-generic callee's frame field starts as the scheduler, a
    -- generic one's as an empty object)
    let childTys := low.fields.drop 2 |>.take sites
    let nps := schedTy :: ps
    let newFields : List Expr := [Suspend.int 0, ← dflt nps ρ] ++ childTys.map (fun τ => match τ with
          | .ref ts _ => if ts.contains nilTag then .heap (.new nilTag) [] else Expr.local 0
          | τ => Expr.lit τ.default) ++
        List.replicate (2 * arms) (Suspend.int 0) ++
        (List.range a).map (fun i => Expr.local (i + 1)) ++ ds.map (Suspend.shift 1) ++
        (← tempTys.mapM (dflt nps))
    -- (the cell starts holding a default of its own type, which may have
    -- fewer type arguments than the override's result, #209)
    let cellDflts : List Expr ← if opened j then (cellResOf j :: more).mapM fun d => do
        pure (.heap (.new resCellTag) [← dflt nps d])
      else pure []
    let newBody : Expr := .heap (.new (tagBase + j)) (newFields ++ cellDflts ++
      (if leafy && isRoot then [.local 0] else []))
    if opened j then
      -- `newCell(params…, cell, sched)`: `new`'s frame, with the parameters
      -- renumbered and the given cell (one per cell the frame keeps, the
      -- others starting as defaults, #209); and its `resumeOwn`, which
      -- writes the result to every cell when it is done
      let renCell (i : Nat) : Nat := if i == 0 then a + 1 else i - 1
      let withCell (l : Nat) : List Expr :=
        newFields.map (Suspend.renumber renCell) ++
          cellDflts.zipIdx.map fun (e, l') => if l' == l then .local a else Suspend.renumber renCell e
      let newCellFn : Fn := { name := s!"{gname}$newCell", arity := a + 2, nslots := a + 2, decides := false,
                              writes := true, body := .heap (.new (tagBase + j)) (withCell 0) }
      ownFns := ownFns.set! (4 * j + 3) newCellFn
      for (_, i) in more.zipIdx do
        ownFns := ownFns.set! (4 * L + moreOff j + i)
          { newCellFn with name := s!"{gname}$newCell{i + 1}", body := .heap (.new (tagBase + j)) (withCell (i + 1)) }
      let pass := (List.range a).map fun i => Expr.heap (.get (Suspend.slotBaseOf sites arms + i)) [.local 0]
      let cellWrites : List Expr := (List.range (1 + more.length)).map fun l =>
        Expr.heap (.set 0) [.heap (.get (cellF + l)) [.local 0], .heap (.get Suspend.resF) [.local 0]]
      let writeAll : Expr := match cellWrites with
        | [w] => w
        | ws => Suspend.seqVoid ws
      let resumeBody : Expr := .seq (Suspend.seqVoid [
        .assign 2 (.call gi (.local 0 :: .local 1 :: pass)),
        .ite (.prim .eq [.local 2, Suspend.int 1]) (.seq writeAll Suspend.vd) Suspend.vd]) (.local 2)
      let resumeOwnFn : Fn := { name := s!"{gname}$resumeOwn", arity := 2, nslots := 3, decides := false,
                                writes := true, body := initPrefixE 2 [Suspend.int 0] resumeBody }
      ownFns := ownFns.set! (4 * j + 1) resumeOwnFn
      ownTys := ownTys.set! (4 * j + 1) [frameTy j, schedTy, .int]
    newFns := newFns.push { name := s!"{gname}$new", arity := a + 1, nslots := a + 1, decides := false,
                            writes := true, body := newBody }
    newTys := newTys.push nps
    -- `g$reset(frame, params…)`: the frame, made ready for another call
    let resetBody := Suspend.seqVoid (.heap (.set Suspend.pcF) [.local 0, Suspend.int 0] ::
      (List.range a).map fun i => .heap (.set (Suspend.slotBaseOf sites arms + i)) [.local 0, .local (i + 1)])
    newFns := newFns.push { name := s!"{gname}$reset", arity := a + 1, nslots := a + 1, decides := false,
                            writes := true, body := resetBody }
    newTys := newTys.push (frameTy j :: ps)
    -- `g$cancel(frame, sched, params…)`: unwinds it
    newFns := newFns.push (← resumeLike s!"{gname}$cancel" low.cancel)
    newTys := newTys.push low.cancel.slots
    if let some i := taskIndex j then
      let some stop := low.stopTasks | throw s!"internal error: {gname} has no source task cleanup"
      taskFns := taskFns.push (← resumeLike s!"{gname}$stopTasks" stop)
      taskTys := taskTys.push stop.slots
      let pass := (List.range a).map fun k => Expr.heap (.get (Suspend.slotBaseOf sites arms + k)) [.local 0]
      taskFns := taskFns.push {
        name := s!"{gname}$stopTasksOwn", arity := 2, nslots := 2, decides := false, writes := true,
        body := .call (taskBase + taskStride * i) (.local 0 :: .local 1 :: pass) }
      taskTys := taskTys.push [frameTy j, schedTy]
      if taskClockF.isSome then
        let some order := low.taskOrder | throw s!"internal error: {gname} has no source task order"
        taskFns := taskFns.push (← resumeLike s!"{gname}$taskOrder" order)
        taskTys := taskTys.push order.slots
        taskFns := taskFns.push {
          name := s!"{gname}$taskOrderOwn", arity := 2, nslots := 2, decides := false, writes := true,
          body := .call (taskBase + taskStride * i + 2) (.local 0 :: .local 1 :: pass) }
        taskTys := taskTys.push [frameTy j, schedTy]
    -- `g$result(frame)`
    newFns := newFns.push { name := s!"{gname}$result", arity := 1, nslots := 1, decides := false,
                            writes := false, body := .heap (.get Suspend.resF) [.local 0] }
    newTys := newTys.push [frameTy j]
    -- the arms of its `sync`s and `race`s
    for ((res, can), i) in low.arms.zipIdx do
      armFns := armFns.push (← resumeLike s!"{gname}$arm{i}" res)
      armFns := armFns.push (← resumeLike s!"{gname}$arm{i}$cancel" can)
      armTys := armTys.push res.slots
      armTys := armTys.push can.slots
      armSigs := armSigs.push (frameTy j :: schedTy :: ps, .int)
      armSigs := armSigs.push (frameTy j :: schedTy :: ps, VTy.void)
    -- its refined calls' helpers (#171), whose slots are their parameters
    -- (one calling a <decides> method can fail too, #179)
    for ((body, vps, vτ), i) in low.vias.zipIdx do
      let canFail := (Suspend.callsOf body).any fun (g, _) =>
        if g < fns.size then ((fns[g]?).map (·.decides)).getD false
        else if selfBase ≤ g then ((selfFns[g - selfBase]?).map (·.decides)).getD false
        else false
      armFns := armFns.push { name := s!"{gname}$via{i}", arity := vps.length, nslots := vps.length,
                              decides := canFail, writes := true, body }
      armTys := armTys.push vps
      armSigs := armSigs.push (vps, vτ)
  -- each root's trampoline, which resumes it with its parameters from its
  -- frame, and `start`, which registers it with the scheduler and runs it
  -- up to its first suspension point (a root that is done has its
  -- suspension point set to -1, and a done root lets the scheduler make
  -- another pass in the same tick, for the tasks waiting for it)
  let mut rootFns : Array Fn := #[]
  let mut rootTys : Array (List VTy) := #[]
  for k in List.range roots.size do
    let j := rootJ k
    let (ri, _, _) := roots[k]!
    let (_, _, sites, arms) := parts[j]!
    let a := fns[ri]!.arity - 2
    let pass := (List.range a).map fun i => Expr.heap (.get (Suspend.slotBaseOf sites arms + i)) [.local 0]
    -- (the task is the root's first parameter; it is marked running while
    -- the root runs, so that cancelling it from inside waits until it
    -- suspends)
    let task : Expr := .heap (.get (Suspend.slotBaseOf sites arms)) [.local 0]
    let trampBody : Expr := Suspend.seqVoid ([
      .heap (.set runningF) [task, .lit (.logic true)],
      .heap (.set curTaskF) [.local 1, task]] ++
      resumeChain (.local 0) (.local 1) (.call ri (.local 0 :: .local 1 :: pass)) topIdx[j]! 2 4 5 ++ [
      .heap (.set curTaskF) [.local 1, .local 3],
      .heap (.set runningF) [task, .lit (.logic false)],
      -- (cancelled while it ran, by itself or by a task it started, #253:
      -- now, unless it ended)
      .ite (.prim .query [.heap (.get cancelReqF) [task]])
        (.seq (Suspend.seqVoid [.heap (.set cancelReqF) [task, .lit (.logic false)],
          .ite (.prim .eq [.local 2, Suspend.int 1]) Suspend.vd
            (.seq (.call cancelRootMark [.local 1, .local 0]) Suspend.vd)]) Suspend.vd) Suspend.vd]) |>
        fun e => Expr.seq e (.local 2)
    rootFns := rootFns.push { name := s!"$spawn{k}$tramp", arity := 2, nslots := if leafy then 6 else 4, decides := false,
                              writes := true, body := initPrefixE 2 ([Suspend.int 0, .heap (.get curTaskF) [.local 1]] ++
                                (if leafy then [Suspend.int 0, Suspend.int 0] else [])) trampBody }
    rootTys := rootTys.push ([frameTy j, schedTy, .int, taskBaseTy] ++ (if leafy then [.int, .int] else []))
    let start : Expr := Suspend.seqVoid ([
      .call linkIdx [.local 0, .local 1],
      .heap (.set rootF) [.heap (.get (Suspend.slotBaseOf sites arms)) [.local 1], .prim .mkSome [.local 1]],
      .assign 3 (.heap (.get cancelCurF) [.local 0]),
      .heap (.set cancelCurF) [.local 0, .lit (.logic false)]] ++
      [.assign 2 (.call (trampOf k) [.local 1, .local 0])] ++ forget (.local 0) ++ [
      takeCancel (.local 1) (.local 2),
      .heap (.set cancelCurF) [.local 0, .local 3],
      .ite (.prim .eq [.local 2, Suspend.int 1])
        (.seq (Suspend.seqVoid [.heap (.set Suspend.pcF) [.local 1, Suspend.int (-1)],
          .heap (.set progressF) [.local 0, .lit (.logic true)], .heap (.set deadF) [.local 0, .lit (.logic true)]])
          Suspend.vd) Suspend.vd])
    rootFns := rootFns.push { name := s!"$spawn{k}$start", arity := 2, nslots := 4, decides := false, writes := true,
                              body := initPrefixE 2 [Suspend.int 0, .lit (.logic false)] start }
    rootTys := rootTys.push [schedTy, frameTy j, .int, .logic]
  -- the scheduler's roots are a list of cells `[root, next]`, so that
  -- adding one costs one cell (an array would be copied, and C keeps every
  -- copy): `$link(sched, root)` adds one at the end
  let cellTag := tagBase + L + B
  let cellTy : VTy := .ref [cellTag] []
  let nextF := 1
  -- (the last cell is read in the condition and written after it: a write
  -- in a condition makes the reference interpreter keep the heap as it
  -- was, for the rollback, and so copy it, once per root, #215; the slot
  -- it is read into starts as a cell of its own, as a slot of a reference
  -- type must)
  let linkBody : Expr := Suspend.seqVoid [
    .ite (.assign 3 (.prim .query [.heap (.get tailF) [.local 0]]))
      (.seq (.heap (.set nextF) [.local 3, .prim .mkSome [.local 2]]) Suspend.vd)
      (.seq (.heap (.set headF) [.local 0, .prim .mkSome [.local 2]]) Suspend.vd),
    .heap (.set tailF) [.local 0, .prim .mkSome [.local 2]]]
  let linkFn : Fn := { name := "$link", arity := 2, nslots := 4, decides := false, writes := true,
                       body := initPrefixE 2 [.heap (.new cellTag) [.local 1, .lit .none],
                         .heap (.new cellTag) [.local 1, .lit .none]] linkBody }
  fns := fns ++ newFns ++ ownFns ++ taskFns ++ selfFns ++ rootFns ++ [linkFn] ++ branchFns ++ armFns
  slotTys := slotTys ++ newTys ++ ownTys ++ taskTys ++ selfTys ++ rootTys ++ [[schedTy, rootAny, cellTy, cellTy]] ++ branchTys ++ armTys
  fsigs := fsigs ++ extraSigs.toList ++ selfSigs.toList ++ rootSigs.toList ++ [([schedTy, rootAny], VTy.void)] ++
    branchSigs.toList ++ armSigs.toList
  -- the wrappers' classes, after the frames', then the cells', then `$nil`
  for K in List.range B do
    frameClasses := frameClasses.push [.int, frameTy branchHome[K]!, taskBaseTy]
    framePins := framePins.push (List.replicate (ntpOfLow branchHome[K]!) none)
  frameClasses := frameClasses.push [rootAny, .opt cellTy]
  framePins := framePins.push []
  frameClasses := frameClasses.push []
  framePins := framePins.push []
  frameClasses := frameClasses.push [.var 0]
  framePins := framePins.push []
  classTable := classTable.set schedTag (((classTable[schedTag]!).set headF (.opt cellTy)).set tailF (.opt cellTy))
  -- cancelling (#156): `$cancelRoot(sched, root)` unwinds a root that is
  -- not done, through its kind's cancel function (a spawned task's root
  -- also marks its task cancelled), and marks it done
  let cancelRootIdx := fns.size
  let cancelTOf (k : Nat) : Nat := cancelRootIdx + 1 + k
  let cancelWOf (K : Nat) : Nat := cancelRootIdx + 1 + roots.size + K
  let dispatchCancel : Expr := (List.range roots.size).foldr (fun k acc =>
      Expr.ite (.heap (.isTag [tagBase + rootJ k]) [.local 1]) (.call (cancelTOf k) [.local 1, .local 0]) acc)
    ((List.range B).foldr (fun K acc =>
      Expr.ite (.heap (.isTag [wrapTag K]) [.local 1]) (.call (cancelWOf K) [.local 1, .local 0]) acc) Suspend.vd)
  let cancelRootBody : Expr := .ite (.prim .ne [.heap (.get Suspend.pcF) [.local 1], Suspend.int (-1)])
    (.seq (Suspend.seqVoid [dispatchCancel, .heap (.set Suspend.pcF) [.local 1, Suspend.int (-1)],
      .heap (.set deadF) [.local 0, .lit (.logic true)], .heap (.set progressF) [.local 0, .lit (.logic true)]])
      Suspend.vd) Suspend.vd
  let cancelRootFn : Fn := { name := "$cancelRoot", arity := 2, nslots := 2, decides := false, writes := true, body := cancelRootBody }
  fns := fns.map fun fn => { fn with body := Suspend.substCall cancelRootMark (fun es => .call cancelRootIdx es) fn.body }
  let mut cancelFns : Array Fn := #[cancelRootFn]
  let mut cancelTys : Array (List VTy) := #[[schedTy, rootAny]]
  let mut cancelSigs : Array (List VTy × VTy) := #[([schedTy, rootAny], VTy.void)]
  for k in List.range roots.size do
    let j := rootJ k
    let (ri, _, _) := roots[k]!
    let (_, _, sites, arms) := parts[j]!
    let a := fns[ri]!.arity - 2
    let pass := (List.range a).map fun i => Expr.heap (.get (Suspend.slotBaseOf sites arms + i)) [.local 0]
    let task : Expr := .heap (.get (Suspend.slotBaseOf sites arms)) [.local 0]
    -- (marked cancelled first: a cancel of it while it unwinds, from a
    -- defer, changes nothing, #261)
    let cbody : Expr := Suspend.seqVoid [.heap (.set tCancelledF) [task, .lit (.logic true)],
      .heap (.set tDoneF) [task, .lit (.logic true)], .call (nFns + 4 * j + 2) (.local 0 :: .local 1 :: pass)]
    let cfn : Fn := { name := s!"$spawn{k}$cancelT", arity := 2, nslots := 2, decides := false, writes := true, body := cbody }
    cancelFns := cancelFns.push cfn
    cancelTys := cancelTys.push [frameTy j, schedTy]
    cancelSigs := cancelSigs.push ([frameTy j, schedTy], VTy.void)
  for K in List.range B do
    let (armRes, doneA, pass) := branchInfo[K]!
    let fr : Expr := .heap (.get 1) [.local 0]
    let pass := pass.map fun e => match e with
      | .heap op _ => Expr.heap op [fr]
      | e => e
    let wbody : Expr := .ite (.prim .eq [.heap (.get doneA) [fr], Suspend.int 0])
      (.seq (Suspend.seqVoid [.heap (.set doneA) [fr, Suspend.int 2], .call (armRes + 1) (fr :: .local 1 :: pass)])
        Suspend.vd) Suspend.vd
    let wfn : Fn := { name := s!"$branch{K}$cancelT", arity := 2, nslots := 2, decides := false, writes := true, body := wbody }
    cancelFns := cancelFns.push wfn
    cancelTys := cancelTys.push [wrapTy K, schedTy]
    cancelSigs := cancelSigs.push ([wrapTy K, schedTy], VTy.void)
  -- `$cancelTaskRoot(sched, task)`: unwinds the task's root, if it has one.
  -- The root is read into a slot in the condition and unwound after it: a
  -- heap write in a condition makes the reference interpreter keep the heap
  -- as it was, for the rollback, and so copy it (#270). The slot has the
  -- roots' type widened by `$nil`, so that its initial value is an empty
  -- object, and the unwinding goes through a test of the roots' classes, to
  -- `$cancelRootSelf(root, sched)`, `$cancelRoot` with its root first.
  let rootW : VTy := .ref (rootAnyTags ++ [nilTag]) []
  let cancelSelfIdx := cancelRootIdx + cancelFns.size
  let cancelTaskRootIdx := cancelSelfIdx + 1
  cancelFns := cancelFns.push { name := "$cancelRootSelf", arity := 2, nslots := 2, decides := false, writes := true,
                                body := .call cancelRootIdx [.local 1, .local 0] }
  cancelTys := cancelTys.push [rootAny, schedTy]
  cancelSigs := cancelSigs.push ([rootAny, schedTy], VTy.void)
  let taskRootBody : Expr := .ite (.assign 2 (.prim .query [.heap (.get rootF) [.local 1]]))
    (.seq (.ite (.heap (.isTag rootAnyTags) [.local 2]) (.call cancelSelfIdx [.local 2, .local 0]) Suspend.vd) Suspend.vd)
    Suspend.vd
  cancelFns := cancelFns.push { name := "$cancelTaskRoot", arity := 2, nslots := 3, decides := false, writes := true,
                                body := initPrefixE 2 [.heap (.new nilTag) []] taskRootBody }
  cancelTys := cancelTys.push [schedTy, taskBaseTy, rootW]
  cancelSigs := cancelSigs.push ([schedTy, taskBaseTy], VTy.void)
  fns := fns.map fun fn => { fn with body := Suspend.substCall cancelTaskRootMark (fun es => .call cancelTaskRootIdx es) fn.body }
  fns := fns ++ cancelFns
  slotTys := slotTys ++ cancelTys
  fsigs := fsigs ++ cancelSigs.toList
  -- (#362) `$resumeAny(frame, sched)` resumes any frame, with its parameters
  -- from itself (its `resumeOwn`, through a dispatch that opens its type
  -- arguments): a root's recorded waiting frame
  let resumeAnyIdx := fns.size
  -- (`$resumeAny(recorded, sched)`: -1 when none is recorded, the
  -- scheduler)
  let resumeAnyBody : Expr := (List.range L).foldr (fun j acc =>
      Expr.ite (.heap (.isTag [tagBase + j]) [.local 0]) (.call (ownBase + 4 * j + 1) [.local 0, .local 1]) acc)
    (Suspend.int (-1))
  if leafy then
    fns := fns.push { name := "$resumeAny", arity := 2, nslots := 2, decides := false, writes := true,
                      body := resumeAnyBody }
    slotTys := slotTys.push [parTy, schedTy]
    fsigs := fsigs ++ [([parTy, schedTy], .int)]
  -- `T.Cancel()` (the mark `$cancelMark(T)`, in suspends code, whose slot 1
  -- is the scheduler): a task that is not done is cancelled now, or, when
  -- it is the one running (it cancels itself), at its next suspension
  let cancelMark := idxOf "$cancelMark"
  let cancelAt (t : Expr) : Expr :=
    .ite (.prim .eq [.heap (.get tDoneF) [t], .lit (.logic false)])
      (.seq (.ite (.prim .query [.heap (.get runningF) [t]])
        (.seq (.heap (.set cancelReqF) [t, .lit (.logic true)]) Suspend.vd)
        (.seq (.call cancelTaskRootIdx [.local 1, t]) Suspend.vd)) Suspend.vd) Suspend.vd
  let replCancel : List Expr → Expr := fun es => match es with
    | [t] => cancelAt t
    | _ => .prim .userErr []
  fns := fns.map fun fn => { fn with body := Suspend.substCall cancelMark replCancel fn.body }
  -- a suspends `Main` runs under the scheduler: a loop of ticks; in each,
  -- passes that resume `Main` and then every root that is not done, again
  -- while a root ends; between ticks the clock moves to the earliest tick
  -- a sleeping task waits for (none: no task can go on)
  if mainSig.suspends then
    let j := mainJ
    let runIdx := fns.size
    let sch : Expr := .local 0
    -- slots: sched, Main's frame, a status, Main done, a root, the next
    -- cell, a cell, another cell (a root that ended is recorded in the
    -- scheduler's `deadF`)
    let st := 2
    let mainDone := 3
    let r := 4
    let cur := 5
    let c := 6
    let n := 7
    let dispatch : Expr := ((List.range roots.size).foldr (fun k acc =>
      Expr.ite (.heap (.isTag [tagBase + rootJ k]) [.local r]) (.call (trampOf k) [.local r, sch]) acc)
      ((List.range B).foldr (fun K acc =>
        Expr.ite (.heap (.isTag [wrapTag K]) [.local r]) (.call (wrapFnBase + 3 * K) [.local r, sch]) acc)
        (.prim .userErr [])))
    let rootOf (cell : Expr) : Expr := .heap (.get 0) [cell]
    let dead (cell : Expr) : Expr := .prim .eq [.heap (.get Suspend.pcF) [rootOf cell], Suspend.int (-1)]
    -- (each cell's next is read after its root ran, so that the roots it
    -- added run in this pass too)
    let pollRoots : List Expr := if rootTags.isEmpty then [] else [
      .assign cur (.heap (.get headF) [sch]),
      .loop (Suspend.seqVoid [
        .ite (.assign c (.prim .query [.local cur])) Suspend.vd .brk,
        .assign r (rootOf (.local c)),
        .ite (.prim .ne [.heap (.get Suspend.pcF) [.local r], Suspend.int (-1)])
          (.seq (Suspend.seqVoid [.assign st dispatch,
            -- (a root asked to be cancelled, awaiting a cancelled task,
            -- unless it ended in that run)
            .ite (.prim .query [.heap (.get cancelCurF) [sch]])
              (.seq (Suspend.seqVoid [.heap (.set cancelCurF) [sch, .lit (.logic false)],
                .ite (.prim .eq [.local st, Suspend.int 1]) Suspend.vd
                  (.seq (.call cancelRootIdx [sch, .local r]) Suspend.vd)]) Suspend.vd) Suspend.vd,
            .ite (.prim .eq [.local st, Suspend.int 1])
              (.seq (Suspend.seqVoid [.heap (.set Suspend.pcF) [.local r, Suspend.int (-1)],
                .heap (.set progressF) [sch, .lit (.logic true)], .heap (.set deadF) [sch, .lit (.logic true)]]) Suspend.vd)
              Suspend.vd]) Suspend.vd) Suspend.vd,
        .assign cur (.heap (.get nextF) [.local c])])]
    let pass : Expr := .loop (Suspend.seqVoid ([
      .heap (.set progressF) [sch, .lit (.logic false)],
      .heap (.set 1) [sch, Suspend.int (-1)],
      ] ++ resumeChain (.local 1) sch (.call mainSig.idx [.local 1, sch]) topIdx[j]! st 8 9 ++ [
      .ite (.prim .eq [.local st, Suspend.int 1]) (.seq (.assign mainDone (Suspend.int 1)) .brk) Suspend.vd,
      -- (`Main` awaited a cancelled task: it is cancelled, and so the program ends)
      .ite (.prim .query [.heap (.get cancelCurF) [sch]])
        (.seq (Suspend.seqVoid [.heap (.set cancelCurF) [sch, .lit (.logic false)],
          .call (nFns + 4 * j + 2) [.local 1, sch], .assign mainDone (Suspend.int 1)]) .brk) Suspend.vd] ++
      pollRoots ++
      [.ite (.prim .query [.heap (.get progressF) [sch]]) Suspend.vd .brk]))
    -- (between ticks, after a root ended, the cells of the roots that are
    -- done are unlinked: no allocation but the new end)
    let compact : List Expr := if rootTags.isEmpty then [] else [
      .ite (.prim .query [.heap (.get deadF) [sch]]) (.seq (Suspend.seqVoid [
        .heap (.set deadF) [sch, .lit (.logic false)],
        .loop (Suspend.seqVoid [
          .ite (.assign c (.prim .query [.heap (.get headF) [sch]])) Suspend.vd .brk,
          .ite (dead (.local c)) (.seq (.heap (.set headF) [sch, .heap (.get nextF) [.local c]]) Suspend.vd) .brk]),
        .ite (.assign c (.prim .query [.heap (.get headF) [sch]]))
          (.seq (Suspend.seqVoid [
            .loop (Suspend.seqVoid [
              .ite (.assign n (.prim .query [.heap (.get nextF) [.local c]])) Suspend.vd .brk,
              .ite (dead (.local n))
                (.seq (.heap (.set nextF) [.local c, .heap (.get nextF) [.local n]]) Suspend.vd)
                (.seq (.assign c (.local n)) Suspend.vd)]),
            .heap (.set tailF) [sch, .prim .mkSome [.local c]]]) Suspend.vd)
          (.seq (.heap (.set tailF) [sch, .lit .none]) Suspend.vd)]) Suspend.vd) Suspend.vd]
    let run : Expr := Suspend.seqVoid [.loop (Suspend.seqVoid (compact ++ [pass,
      .ite (.prim .eq [.local mainDone, Suspend.int 1]) .brk Suspend.vd,
      .ite (.prim .lt [.heap (.get 1) [sch], Suspend.int 0]) (.seq (.prim .userErr []) Suspend.vd) Suspend.vd,
      .heap (.set 0) [sch, .heap (.get 1) [sch]]]))]
    let cellInit : Expr := .heap (.new cellTag) [.local 1, .lit .none]
    fns := fns.push { name := "$Run", arity := 2, nslots := if leafy then 10 else 8, decides := false, writes := true,
                      body := initPrefixE 2 ([Suspend.int 0, Suspend.int 0, .local 1, .lit .none,
                        cellInit, cellInit] ++ (if leafy then [Suspend.int 0, Suspend.int 0] else [])) run }
    slotTys := slotTys.push ([schedTy, frameTy j, .int, .int, rootAny, .opt cellTy, cellTy, cellTy] ++
      (if leafy then [.int, .int] else []))
    fsigs := fsigs ++ [([schedTy, frameTy j], VTy.void)]
    -- (the prelude calls a function without arguments, `checkPrelude`)
    -- (the scheduler is its class's prototype, so that immediate code can
    -- spawn on it)
    fns := fns.push { name := "$Start", arity := 0, nslots := 0, decides := false, writes := true,
                      body := .call runIdx [schedLit, .call (nFns + 4 * j) [schedLit]] }
    slotTys := slotTys.push []
    fsigs := fsigs ++ [([], VTy.void)]
    mainCall := .call (runIdx + 1) []
  fns := fns.map fun fn => { fn with body := Suspend.substCall resumeAnyMark (fun es => .call resumeAnyIdx es) fn.body }
  -- (and the values of the scheduler's fields it adds, #362, for its prototype)
  return (fns, slotTys, fsigs, classTable, frameClasses, mainCall, framePins.toList,
    (if leafy then [(match schedLit with | .lit v => v | _ => .none), .int (-1)] else []) ++
      (if taskClockF.isSome then [.int 0] else []))

/-- Whether `e` itself prints (`Print`), for `checkEager`. -/
partial def exprPrints : Expr → Bool
  | .print _ => true
  | .assign _ e | .ret e | .loop e => exprPrints e
  | .seq a b => exprPrints a || exprPrints b
  | .prim _ es | .heap _ es | .call _ es => es.any exprPrints
  | .ite c t e => exprPrints c || exprPrints t || exprPrints e
  | .forE _ it f b => exprPrints it || exprPrints f || exprPrints b
  | _ => false

/-- A function's name as messages show it: a `block:`'s by its class. -/
def shownFn (n : String) : String :=
  if n.endsWith ".$block" then s!"the block: of {String.ofList (n.toList.take (n.length - 7))}" else n

/-- (#235) A recursive function with several values is computed at its
    call as `F$all`, all its values at once, so nothing it may run may print
    or call `Err()`. Followed through its Verse Core code, so through every
    call it may make: functions, methods (each implementation a dispatch
    may pick), function values (each function of that type used as a
    value), constructors (field defaults, `block:` clauses), constants, and
    parameter defaults (elaborated at the call). `errs` says where each
    function elaborated from the program calls `Err()`. -/
def checkEager (fns : Array Fn) (errs : Array (Option Pos)) (posOf : String → Option Pos) :
    Except String Unit := do
  for i in List.range fns.size do
    let fn := fns[i]!
    if !fn.name.endsWith "$all" then continue
    let g := String.ofList (fn.name.toList.take (fn.name.length - 4))
    let loc := ((posOf g).map (·.show ++ ": ")).getD ""
    let mut seen : Array Bool := Array.replicate fns.size false
    let mut todo : List Nat := [i]
    seen := seen.set! i true
    while !todo.isEmpty do
      let j := todo.head!
      todo := todo.tail!
      let fj := fns[j]!
      let via := if fj.name == fn.name then "" else s!" ({shownFn fj.name} does)"
      let what? : Option String :=
        if exprPrints fj.body then some "print"
        else if let some (some _) := errs[j]? then some "call Err()" else none
      if let some what := what? then
        throw s!"{loc}{g} has several values and is recursive, or called by a recursive one, and it may {what}{via}: such a function must be <computes>, keep no local state, and reach nothing that prints or calls Err(), as all its values are computed at a call (#235)"
      for (f, _) in Suspend.callsOf fj.body do
        if f < fns.size && !seen[f]! then
          seen := seen.set! f true
          todo := todo ++ [f]

/-- Whether `e` itself changes an object (a field's `set`). -/
partial def exprWrites : Expr → Bool
  | .heap (.set _) _ => true
  | .assign _ e | .ret e | .loop e | .print e => exprWrites e
  | .seq a b => exprWrites a || exprWrites b
  | .prim _ es | .heap _ es | .call _ es => es.any exprWrites
  | .ite c t e => exprWrites c || exprWrites t || exprWrites e
  | .forE _ it f b => exprWrites it || exprWrites f || exprWrites b
  | _ => false

/-- (#246) A recursive function with several values that a context taking
    its first success consumes lazily runs the code of an item (its
    clauses, conditions and the arguments of its calls of itself) once for
    all the values the item gives: so that code may not print or change an
    object, whose effects for values the context then rejects would stay,
    where the Verse Calculus undoes them with those values. (Its values are
    computed in the context's own failure context: undone with it.) -/
def checkLoopFirst (fns : Array Fn) (uses : List LoopUse)
    (registered : List Choice.FirstLift := []) : Except String (List Choice.FirstLift) := do
  -- A continuation replaces the lazy call's suffix. Install these first so
  -- effectful lazy helpers are requested for the prepared suffix they will
  -- actually consume, rather than also keeping obsolete copies from trials.
  let continuations := uses.foldl (fun acc u => match u.g, u.lift with
    | "", .ok l =>
      if registered.any (·.key == l.key) || acc.any (·.key == l.key) then acc else acc ++ [l]
    | _, _ => acc) ([] : List Choice.FirstLift)
  if !continuations.isEmpty then return continuations
  let mut needs : List Choice.FirstLift := []
  for u in uses do
    -- (a continuation, #335: asked for whenever it could be made; when not,
    -- the clauses were copied)
    if u.g == "" then
      if let .ok l := u.lift then
        if !needs.any (·.key == l.key) then needs := needs ++ [l]
      continue
    let g := u.g
    let e := u.itemCode
    let why (what via : String) : String :=
      s!"{u.pos.show}: {g} has several values, is recursive and may {what}{via} in its clauses, its conditions or the arguments of its calls of itself: in a context that takes its first success, that code runs once for all the values it leads to, and what it does for values the context then rejects would stay"
    let mut msg? : Option String := none
    if let some q := u.argSet then
      msg? := some s!"{q.show}: a set in an argument of {g}'s call of itself: where the first success is taken, it would not be undone with the values of that call that the context rejects"
    else if exprPrints e then msg? := some (why "print" "")
    else if exprWrites e then msg? := some (why "change an object" "")
    else
      let mut seen : Array Bool := Array.replicate fns.size false
      let mut todo : List Nat := []
      for (f, _) in Suspend.callsOf e do
        if f < fns.size && !seen[f]! then
          seen := seen.set! f true
          todo := todo ++ [f]
      while !todo.isEmpty && msg?.isNone do
        let j := todo.head!
        todo := todo.tail!
        let fj := fns[j]!
        if exprPrints fj.body then msg? := some (why "print" s!" ({shownFn fj.name} does)")
        else if exprWrites fj.body then msg? := some (why "change an object" s!" ({shownFn fj.name} does)")
        for (f, _) in Suspend.callsOf fj.body do
          if f < fns.size && !seen[f]! then
            seen := seen.set! f true
            todo := todo ++ [f]
    -- (such a call is compiled as a function of its own, recursive, which
    -- undoes it as the Verse Calculus does, where it can be)
    if let some msg := msg? then
      match u.lift with
      | .ok l => if !needs.any (·.key == l.key) then needs := needs ++ [l]
      | .error reason =>
        throw s!"{msg}; it would be compiled as a function of its own, which is not supported {reason} yet: call {g} in a for, or move that into its values (#246)"
  return needs

/-- Elaborate a parsed program into a Verse Core program that passes `Prog.check`
    and `Prog.checkTypes`. -/
def elabProgramCore (allTops0r : List STop) (opts : Options := {}) : Except String Compiled := do
  SourceProfile.check opts.profile allTops0r opts.entry
  -- rationals (#116): the helpers, for a program that may use them
  let isRatMarker : STop → Bool := fun
    | .const _ n _ _ => n == ratMarker || n == replaceAllMarker
    | _ => false
  let usesReplaceAll := allTops0r.any (fun | .const _ n _ _ => n == replaceAllMarker | _ => false) || opts.entry.isSome
  let usesRat := allTops0r.any isRatMarker || opts.entry.isSome
  -- (a type of the program's own cannot take a built-in type's name)
  for t in allTops0r do
    match t with
    | .const p n _ (.structDef ..) | .const p n _ (.enumDef ..) | .classDef p n .. =>
      if ("char32" :: typeNames).contains n then throw s!"{p.show}: {n} is a built-in type"
    | _ => pure ()
  let helpers ← if usesRat then ratTops else pure []
  let helpers := helpers ++ (← if usesReplaceAll then replaceAllTops else pure [])
  -- concurrency (#156): the helpers, for a program with a <suspends> function
  -- (and `subscribable_event`, which extends the concurrency prelude's
  -- `event`, #210)
  -- (unless the program defines its own)
  let defines0 (n : String) : Option Pos := allTops0r.findSome? fun
    | .classDef p m .. | .fn p m .. | .const p m .. => if m == n then some p else none
  let usesSubVoid := (defines0 "subscribable_event").isNone && allTops0r.any (·.usesType "$subev0")
  let usesSub := usesSubVoid || (defines0 "subscribable_event").isNone && allTops0r.any (·.usesType "subscribable_event")
  if usesSub then
    if let some p := defines0 "cancelable" then
      throw s!"{p.show}: cancelable is the type subscribable_event's Subscribe gives: a program that uses subscribable_event cannot define its own (#210)"
  let usesConc := usesSub || allTops0r.any fun
    | .fn _ _ _ _ effs _ _ => effs.contains "suspends"
    | .classDef _ _ _ _ _ _ _ _ ms => ms.any fun
      | .fn _ _ _ _ effs _ _ => effs.contains "suspends"
      | _ => false
    | _ => false
  let helpers := helpers ++ (← if usesConc then concTops else pure []) ++ (← if usesSub then subTops else pure []) ++
    (← if usesSubVoid then subVoidTops else pure [])
  let allTops000 := allTops0r.filter (!isRatMarker ·)
  -- modules (#112): every reference to a member, qualified (the entry
  -- expression's too)
  let rawEntry : List STop := match opts.entry with
    | some e => [.fn e.pos "$Do" [] [] ["decides"] (.name "void") (.app e.pos (.ident e.pos "$Show") [e] false)]
    | none => []
  let resolved ← resolveModules (allTops000 ++ rawEntry)
  -- functions with several values (#235): inlined at their calls
  -- (#283) the members of built-in types and of the prelude: a method with
  -- several values may not be named like one, as `R.M` could be it
  let reserved : List String := ["Length", "Slice", "Find", "Insert", "Remove", "RemoveElement",
    "RemoveFirstElement", "RemoveAllElements", "ReplaceElement", "ReplaceAllElements", "ReplaceAll", "Last",
    "Signal", "Await", "Cancel"] ++ helpers.flatMap fun
      | .classDef _ _ _ _ _ _ fs _ ms => fs.map (·.1) ++ ms.filterMap fun | .fn _ m .. => some m | _ => none
      | _ => []
  let (resolved, lazy) ← Choice.inlineMulti resolved reserved opts.eagerRequests
  -- (#246) the class of the stack cells of lazily taken ones
  let helpers := helpers ++ (← if lazy then lazyTops else pure [])
  -- the branches of casts that refine type arguments, as functions (#243)
  -- (in front, as the entry expression is the end)
  let resolved := Refine.functions opts.castRequests resolved ++ resolved
  -- (#246) the functions of their own of lazily taken calls
  let resolved := opts.loopRequests.flatMap (fun l =>
    (if l.stageOnly then [] else [STop.fn l.pos l.name l.params l.tparams l.specs l.ret l.body]) ++ l.extraFns) ++ resolved
  -- (the helpers after: they name nothing of the program's)
  -- function values (#210): the function types' interfaces, and a class
  -- for each function used as a value
  -- (the entry expression is scanned too)
  let allTops00 := copyIfaceDefaults (FnValues.desugar (resolved.take (resolved.length - rawEntry.length) ++ helpers)
    (resolved.drop (resolved.length - rawEntry.length)) (opts.fnRequests.map fun (n, t) => (n, t.toSTy)) opts.methodRequests)
  let entryTop := resolved.drop (resolved.length - rawEntry.length)
  -- the command line: `Args`, and an entry expression
  let defines (n : String) := allTops00.any fun
    | .fn _ m .. | .const _ m .. | .classDef _ m .. => m == n
  let argsTop : List STop :=
    match opts.args with
    | some as =>
      if defines "Args" then []
      else [.const { line := 0, col := 0 } "Args" (some (.arr (.name "string")))
              (.arrayLit { line := 0, col := 0 } (as.map fun a => .str { line := 0, col := 0 } [.text a]))]
    | none => []
  -- overloaded methods (#106): a method name declared with two or more
  -- parameter lists is renamed, in every class and interface, by its list
  -- (`M$ovN`): an override has its method's list, so its name too
  -- (up to the names of type parameters: the class's and the method's own,
  -- each by its place, so a generic override that renames them has its
  -- method's list)
  let sigText (ctps : List TParam) (mtps : List TParam) (ps : List SParam) : String :=
    let ρ : List (String × STy) :=
      ((ctps.zip (List.range ctps.length)).map fun (tp, i) => (tp.name, STy.name s!"$c{i}")) ++
      ((mtps.zip (List.range mtps.length)).map fun (tp, i) => (tp.name, STy.name s!"$m{i}"))
    -- (and `string` is `[]char`)
    let ρ := ρ ++ [("string", STy.arr (.name "char"))]
    reprStr (ps.map fun q => (q.named, if q.named then q.name else "", q.ty.substNames ρ))
  -- (per class hierarchy: classes and interfaces connected by inheritance,
  -- so unrelated classes' methods of one name are not overloads)
  let classDefs : List (String × List TParam × List STy × List STop) :=
    (allTops00 ++ argsTop ++ entryTop).filterMap fun
      | .classDef _ n tps _ parents _ _ _ methods => some (n, tps, parents, methods)
      | _ => none
  let parentName : STy → Option String := fun | .name q => some q | .app q _ => some q | _ => none
  let mut hier : List (String × String) := classDefs.map fun (n, _) => (n, n)
  for _ in [0:classDefs.length + 1] do
    -- (until a pass joins nothing: a pass per class made it cubic)
    let mut joined := false
    for (n, _, ps, _) in classDefs do
      for q in ps.filterMap parentName do
        match hier.lookup n, hier.lookup q with
        | some a, some b =>
          if a != b then
            let r := if a < b then a else b
            hier := hier.map fun (x, h) => if h == a || h == b then (x, r) else (x, h)
            joined := true
        | _, _ => pure ()
    if !joined then break
  let hierOf (n : String) : String := (hier.lookup n).getD n
  -- each class's ancestors (itself first), each with its type parameters in
  -- the class's terms
  let infoOf (n : String) := (classDefs.find? (·.1 == n)).map fun (_, tps, ps, ms) => (tps, ps, ms)
  let mut anc : List (String × List (String × List (String × STy))) :=
    classDefs.map fun (n, _) => (n, [(n, [])])
  for _ in [0:classDefs.length + 1] do
    let mut changed := false
    for (n, _, ps, _) in classDefs do
      let mine := (anc.lookup n).getD []
      let mut add : List (String × List (String × STy)) := []
      for pty in ps do
        let (q, args) := match pty with | .app q as => (q, as) | .name q => (q, []) | _ => ("", [])
        let qtps := ((infoOf q).map (·.1)).getD []
        let σq : List (String × STy) := (qtps.map (·.name)).zip args
        for (y, σy) in (anc.lookup q).getD [] do
          if !(mine ++ add).any (·.1 == y) then
            let σ := if y == q then σq else σy.map fun (v, t) => (v, t.substNames σq)
            add := add ++ [(y, σ)]
      if !add.isEmpty then
        anc := anc.map fun (x, a) => if x == n then (x, a ++ add) else (x, a)
        changed := true
    if !changed then break
  -- the non-override declarations of a method in a class: its lists
  let ownLists (y mn : String) : List (List TParam × List SParam) := ((infoOf y).map fun (_, _, ms) =>
    ms.filterMap fun
      | .fn _ x ps mtps effs .. => if x == mn && !effs.contains "override" then some (mtps, ps) else none
      | _ => none).getD []
  let decls : List ((String × String) × String) := classDefs.flatMap fun (cn, ctps, _, methods) =>
    methods.filterMap fun
      -- (an override joins its method's list: only the others make lists)
      | .fn _ mn ps mtps effs .. =>
        if mn == "$block" || mn.startsWith "(" || effs.contains "override" then none
        else some ((hierOf cn, mn), sigText ctps mtps ps)
      | _ => none
  let keys := (decls.map (·.1)).eraseDups
  -- (a name is overloaded where some class's ancestors declare two or more
  -- of its lists: siblings' own lists are not overloads)
  let listsSeen (n mn : String) : List String :=
    (((anc.lookup n).getD []).flatMap fun (y, _) =>
      let ytps := ((infoOf y).map (·.1)).getD []
      (ownLists y mn).map fun (mtps, ps) => sigText ytps mtps ps).eraseDups
  let mov : List ((String × String) × List String) := keys.filterMap fun key =>
    let sigs := ((decls.filter (·.1 == key)).map (·.2)).eraseDups
    if sigs.length > 1 && classDefs.any (fun (n, _) => hierOf n == key.1 && (listsSeen n key.2).length > 1) then
      some (key, sigs)
    else none
  let mangle (cn mn : String) (ctps mtps : List TParam) (ps : List SParam) (isOverride : Bool)
      (within : Option String) : String :=
    match mov.lookup (hierOf cn, mn) with
    | none => mn
    | some sigs =>
      if !isOverride then s!"{mn}$ov{(sigs.idxOf? (sigText ctps mtps ps)).getD 0}"
      else
        -- an override: the ancestor list it has, each in this class's terms
        -- (through the type arguments the class gives its parents)
        let mine := sigText ctps mtps ps
        -- (a qualified `(q:)M`: only `q`'s lists, and those above it)
        let none' : List (String × List (String × STy)) := []
        let ups0 : List (String × List (String × STy)) := ((anc.lookup cn).getD none').drop 1
        let ups : List (String × List (String × STy)) := match within with
          | some q =>
            let above : List String := ((anc.lookup q).getD none').map Prod.fst
            ups0.filter fun u => u.1 == q || above.contains u.1
          | none => ups0
        let cands : List (Nat × String × Nat) := ups.flatMap fun (y, σ) =>
          let ytps := ((infoOf y).map (·.1)).getD []
          (ownLists y mn).filterMap fun (dmtps, dps) =>
            (sigs.idxOf? (sigText ytps dmtps dps)).map fun k =>
              -- (its own type parameters renamed apart first: the class's
              -- arguments must not capture them)
              let apart : List (String × STy) := (dmtps.zip (List.range dmtps.length)).map fun (tp, i) =>
                (tp.name, STy.name s!"$own{i}")
              let dmtps' := (dmtps.zip (List.range dmtps.length)).map fun (tp, i) => { tp with name := s!"$own{i}" }
              (k, sigText ctps dmtps' (dps.map fun q => { q with ty := (q.ty.substNames apart).substNames σ }), dps.length)
        match (cands.filter (·.2.1 == mine)).map (·.1) |>.eraseDups with
        | [k] => s!"{mn}$ov{k}"
        | _ =>
          match (cands.filter (·.2.2 == ps.length)).map (·.1) |>.eraseDups with
          | [k] => s!"{mn}$ov{k}"
          | _ => mn   -- refused below
  let mut tops1 : Array STop := #[]
  for t in allTops00 ++ argsTop ++ entryTop do
    match t with
    | .classDef cp n tps specs parents isI fields ovs methods =>
      let mut ms : Array STop := #[]
      for m in methods do
        match m with
        | .fn mp mn ps mtps effs ret body =>
          -- `(q:)M`, implementing `q`'s overload of `M` that has its list
          -- (#125): `(q:)M$ovK`
          let qual : Option (String × String) := if mn.startsWith "(" then
              match (mn.drop 1).toString.splitOn ":)" with
              | [q, m'] => some (q, m')
              | _ => none
            else none
          match qual with
          | some (q, m') =>
            -- (`q` above the class: otherwise the check below explains)
            let isAbove := (((anc.lookup n).getD []).drop 1).any (·.1 == q)
            if isAbove && (mov.lookup (hierOf n, m')).isSome then
              let k := mangle n m' tps mtps ps true (some q)
              if k == m' then
                throw s!"{mp.show}: ({q}:){m'} must have the parameters of one of {q}'s overloads of {m'}"
              ms := ms.push (.fn mp s!"({q}:){k}" ps mtps effs ret body)
            else ms := ms.push (.fn mp mn ps mtps effs ret body)
          | none =>
            ms := ms.push (.fn mp (mangle n mn tps mtps ps (effs.contains "override") none) ps mtps effs ret body)
        | m => ms := ms.push m
      tops1 := tops1.push (.classDef cp n tps specs parents isI fields ovs ms.toList)
    | t => tops1 := tops1.push t
  let allTops0 := tops1.toList
  -- classes and interfaces (#14, #18): each is a struct whose fields are
  -- those inherited first, then its own; each method `M` of `c` a function
  -- `c.M` whose first parameter is `Self`, generic over the class's type
  -- parameters and then its own; an abstract method one whose body is
  -- unreachable
  let cdefs : List CDef := allTops0.filterMap fun
    | .classDef p n tps specs parents isIface fields overrides methods =>
      let names := parents.map fun | .name q => q | .app q _ => q | _ => "?"
      let args := parents.map fun | .app _ as => as | _ => []
      some { pos := p, name := n, tps, specs, parents := names, parentArgs := args, isIface, fields,
             overrides, methods }
    | _ => none
  let cdef? (n : String) : Option CDef := cdefs.find? (·.name == n)
  let methodNamed (cd : CDef) (m : String) : Option STop := cd.methods.find? fun
    | .fn _ x .. => x == m
    | _ => false
  let declares (n m : String) : Bool := ((cdef? n).bind (methodNamed · m)).isSome
  -- (by the name as written: an overload's is its method's, #106)
  let declaresBase (n m : String) : Bool := ((cdef? n).map fun cd => cd.methods.any fun
    | .fn _ x .. => methodBase x == m
    | _ => false).getD false
  let hasBody (n m : String) : Bool := match (cdef? n).bind (methodNamed · m) with
    | some (.fn _ _ _ _ effs _ _) => !effs.contains "$abstract"
    | _ => false
  -- the hierarchy
  let mut cinfo : Array (String × ClassInfo) := #[]
  for cd in cdefs do
    let p := cd.pos
    for sp in cd.specs do
      match sp with
      | "persistable" | "final_super" => throw s!"{p.show}: <{sp}> classes are not supported yet (#11)"
      | _ => pure ()
    let mut parent : Option String := none
    let mut ifaces : Array String := #[]
    for (q, qargs) in cd.parents.zip cd.parentArgs do
      let some qd := cdef? q
        | if allTops0.any (fun | .const _ n' none (.structDef ..) => n' == q | _ => false) then
            throw s!"{p.show}: {q} is a struct: only classes and interfaces can be inherited from"
          else throw s!"{p.show}: unknown class or interface '{q}'"
      if qargs.length != qd.tps.length then
        throw s!"{p.show}: {q} takes {qd.tps.length} type argument(s), found {qargs.length}"
      -- (an interface that extends a parametric interface may give it any
      -- type arguments: its Verse Core type arguments start with that
      -- interface's at them, as a class's start with its parent's, #53)

      if qd.isIface then ifaces := ifaces.push q
      else
        if cd.isIface then throw s!"{p.show}: interface {cd.name} cannot extend class {q}"
        if parent.isSome then throw s!"{p.show}: class {cd.name} has two superclasses (a class inherits from at most one)"
        if qd.specs.contains "final" then throw s!"{p.show}: class {q} is <final>: it cannot be inherited from"
        parent := some q
    let info : ClassInfo := { parent, ifaces := ifaces.toList, isIface := cd.isIface,
                              isAbstract := cd.specs.contains "abstract", isFinal := cd.specs.contains "final" }
    cinfo := cinfo.push (cd.name, info)
  let henv : TyEnv := { classes := cdefs.map (·.name), cinfo := cinfo.toList,
                        cinfoMap := cinfo.foldl (fun m (n, i) => m.insert n i) {} }
  let henv : TyEnv := { henv with supersMap := henv.classes.foldl (fun m d => m.insert d (henv.supers d)) {} }
  let directUp (n : String) : List String := (henv.info n).parent.toList ++ (henv.info n).ifaces
  for cd in cdefs do
    let mut seen : List String := []
    let mut frontier := directUp cd.name
    for _ in [0:cdefs.length + 1] do
      let new := frontier.filter (!seen.contains ·)
      seen := seen ++ new
      frontier := new.flatMap directUp
    if seen.contains cd.name then throw s!"{cd.pos.show}: {cd.name} inherits from itself"
  -- the type arguments `c` gives `T` above it, as written in terms of `c`'s
  -- type parameters (through parents of both kinds, #39, #53)
  let supArgsSTy (c T : String) : Option (List STy) := Id.run do
    let mut frontier : List (String × List STy) :=
      [(c, ((cdef? c).map fun cd => cd.tps.map fun tp => STy.name tp.name).getD [])]
    for _ in [0:cdefs.length + 1] do
      if let some (_, a) := frontier.find? (·.1 == T) then return some a
      frontier := frontier.flatMap fun (x, xa) => match cdef? x with
        | some xd =>
          let σ := (xd.tps.map (·.name)).zip xa
          (xd.parents.zip xd.parentArgs).map fun (q, qa) => (q, qa.map (·.substNames σ))
        | none => []
    return none
  -- the fields of each class: its superclass's, then those of the
  -- interfaces above it that are not there yet (once, along a diamond), then
  -- its own (an `<override>` field gives an inherited one a new default)
  let mut full : Array (String × List (String × STy × Option SExpr × Bool)) := #[]
  let mut fieldOverrides : Array (Pos × String × String × STy) := #[]
  let mut defaultClashes : Array String := #[]
  -- (each class's fields by name too: lookups in `full` made this cubic)
  let mut fullMap : Std.HashMap String (List (String × STy × Option SExpr × Bool)) := {}
  for _ in [0:cdefs.length + 1] do
    -- (until a pass resolves nothing more, or every class is resolved)
    if full.size == cdefs.length then break
    let before := full.size
    for cd in cdefs do
      if fullMap.contains cd.name then continue
      let inherited? : Option (List (String × STy × Option SExpr × Bool)) :=
        match (henv.info cd.name).parent with
        | none => some []
        | some q =>
          -- in terms of this class's type parameters (#39)
          let qargs := ((cd.parents.zip cd.parentArgs).lookup q).getD []
          let σ := ((((cdef? q).map (·.tps)).getD []).map (·.name)).zip qargs
          fullMap[q]?.map fun fs => fs.map fun (f, sty, d, v) => (f, sty.substNames σ, d, v)
      let some inh := inherited? | continue
      -- the interfaces above must be resolved first
      let ifacesUp := ((henv.supers cd.name).drop 1).filter (henv.info · |>.isIface)
      if ifacesUp.any (fun i => !fullMap.contains i) then continue
      let mut fs : List (String × STy × Option SExpr × Bool) := inh
      -- each interface field not inherited through the class chain, once; its
      -- default is that of the most specific interface that gives one (as for
      -- methods, whatever the order of the parents)
      for i in ifacesUp do
        -- (in terms of this class's type parameters, #53)
        let iσ := ((((cdef? i).map (·.tps)).getD []).map (·.name)).zip ((supArgsSTy cd.name i).getD [])
        for (f, sty0, _, isVar) in fullMap[i]?.getD [] do
          let sty := sty0.substNames iσ
          if ((henv.supers cd.name).drop 1).any (declares · f) then
            throw s!"{cd.pos.show}: field '{f}' of {cd.name} has the name of an inherited method"
          if let some (_, _, _, v0) := fs.find? (·.1 == f) then
            -- reached again: its type must agree (checked once types are
            -- resolved), and whether it is a var
            if v0 != isVar then
              throw s!"{cd.pos.show}: {cd.name} inherits field '{f}' as a var from one parent and not from another"
            fieldOverrides := fieldOverrides.push (cd.pos, cd.name, f, sty)
          else
            -- the interfaces that give the field a default themselves (an
            -- inherited default is its declaring interface's)
            let ownDefault (j : String) : Option SExpr :=
              (((cdef? j).map (·.fields)).getD []).findSome? fun (g, _, d, _) => if g == f then d else none
            let withDefault := ifacesUp.filter fun j => (ownDefault j).isSome
            let best := withDefault.filter fun j => !withDefault.any fun j' => j' != j && henv.isSub j' j
            if best.length > 1 && !cd.overrides.contains f then
              defaultClashes := defaultClashes.push
                s!"{cd.pos.show}: {cd.name} inherits a default for field '{f}' from both {best[0]!} and {best[1]!}: give it one with {f}<override>:t = e"
            let d := best.head?.bind ownDefault
            fs := fs ++ [(f, sty, d, isVar)]
      for (f, sty, d, isVar) in cd.fields do
        if f == "Self" then throw s!"{cd.pos.show}: a field of {cd.name} cannot be called Self"
        if ((henv.supers cd.name).drop 1).any (declares · f) then
          throw s!"{cd.pos.show}: field '{f}' of {cd.name} has the name of an inherited method"
        match fs.findIdx? (fun (g : String × STy × Option SExpr × Bool) => g.1 == f) with
        | some k =>
          if cd.overrides.contains f && d.isNone then
            throw s!"{cd.pos.show}: {f}<override> must give a new default: write {f}<override>:t = e"
          if !cd.overrides.contains f then
            throw s!"{cd.pos.show}: field '{f}' of {cd.name} has the name of an inherited field (write {f}<override>:t = … to give it a new default)"
          let (_, sty0, _, v0) := fs[k]!
          if isVar != v0 then
            throw s!"{cd.pos.show}: {f}<override> cannot change whether the field is a var"
          fs := fs.set k (f, sty0, d, v0)
          fieldOverrides := fieldOverrides.push (cd.pos, cd.name, f, sty)
        | none =>
          if cd.overrides.contains f then
            throw s!"{cd.pos.show}: {f}<override> in {cd.name} does not override an inherited field"
          fs := fs ++ [(f, sty, d, isVar)]
      -- (#209) each type parameter that is not one of its parent's type
      -- arguments as a whole: a hidden field holds a value of it, from
      -- which a method of the class, run by a dispatch that opens it, gets
      -- its slots of that type (`Sig.selfTps`)
      -- (only where an override, at or below, may need it)
      let methodsBelow := cdefs.any fun cd' => henv.isSub cd'.name cd.name &&
        cd'.methods.any fun | .fn _ _ _ _ effs .. => effs.contains "override" | _ => false
      -- (#250: or a cast that opens them targets the class or one below it,
      -- whose branch's function reads them from the object, also those an
      -- ancestor of the target adds)
      let methodsBelow := methodsBelow || opts.witnessAll.contains cd.name ||
        opts.castRequests.any fun l => !l.opened.isEmpty && henv.isSub l.target cd.name
      -- (#276, #209: a root class counts them as `rootArgCount` does: the
      -- first of its Verse Core type arguments, as many as the interface
      -- with the fewest type parameters at or above it, or above a class
      -- below it that leaves one of the others a type parameter; an
      -- interface has no such fields)
      let qargs? : Option (List STy) := if cd.isIface then none else
        if opts.witnessAll.contains cd.name then some [] else match (henv.info cd.name).parent with
        | some q => some (((cd.parents.zip cd.parentArgs).lookup q).getD [])
        | none =>
          -- (the interfaces above it or above a class below it, #209)
          let below := cdefs.filter fun c => !c.isIface && henv.isSub c.name cd.name
          let ifs := cdefs.filter fun i => i.isIface && below.any fun c => henv.isSub c.name i.name
          if ifs.isEmpty then none else
          -- (its Verse Core type arguments: those it gives the interface it
          -- lists with the most, then its other type parameters, as
          -- `coreArgs` has them; all of them when it lists no interface)
          -- (each at that interface's Verse Core type arguments, also those
          -- it gives its own parents, #53)
          let longest := ((cd.parents.zip cd.parentArgs).filter fun (q, _) => (henv.info q).isIface).foldl
            (fun (b : List STy) (q, qa) =>
              let qa := match cdefs.find? (·.name == q) with
                | some qd => qd.ifaceCoreS cdefs qa
                | none => qa
              if b.length < qa.length then qa else b) []
          let others := cd.tps.filter fun tp => !longest.any fun | .name v => v == tp.name | _ => false
          let coreS := longest ++ others.map fun tp => STy.name tp.name
          -- (#351: an interface it lists at type arguments that are not a
          -- prefix of its own is referred to through views, a dispatch
          -- through which may open any of them: all have hidden fields)
          let nonPrefix := (cd.parents.zip cd.parentArgs).any fun (q, qa) =>
            (henv.info q).isIface &&
              let ca := match cdefs.find? (·.name == q) with
                | some qd => qd.ifaceCoreS cdefs qa
                | none => qa
              !(ca.length ≤ coreS.length && (ca.zip coreS).all fun (a, b) => Choice.styEq a b)
          if nonPrefix then some [] else
          -- (as a class below gives them: through its parents' arguments)
          let rec viewIn (fuel : Nat) (c : CDef) : List STy :=
            match fuel with
            | 0 => coreS
            | f + 1 =>
              if c.name == cd.name then coreS else
              match (henv.info c.name).parent with
              | some q => match cdefs.find? (·.name == q) with
                | some qd =>
                  let σ := qd.tps.map (·.name) |>.zip (((c.parents.zip c.parentArgs).lookup q).getD [])
                  (viewIn f qd).map (·.substNames σ)
                | none => coreS
              | none => coreS
          -- (an interface above a class below it counts only when one of
          -- its type arguments that interface does not give is still a
          -- type parameter there, as `rootArgCount` has it, #276)
          let fewest := below.foldl (fun m c =>
            let view := viewIn cdefs.length c
            (ifs.filter fun i => henv.isSub c.name i.name).foldl (fun m i =>
              let k := i.tps.length
              if c.name == cd.name || (view.drop k).any (STy.mentionsAny (c.tps.map (·.name))) then min m k else m) m)
            coreS.length
          some (coreS.take fewest)
      if let some qargs := qargs? then
        for tp in (if methodsBelow then cd.tps else []) do
          -- (all of them for a class with a class parent that lists an
          -- interface at type arguments that are not a prefix of its own,
          -- which a dispatch through a view opens, #351)
          if opts.witnessAll.contains cd.name || !qargs.any (fun | .name v => v == tp.name | _ => false) then
            fs := fs ++ [(s!"$w.{cd.name}.{tp.name}", .name tp.name, some (.ident cd.pos "$witness"), false)]
      full := full.push (cd.name, fs)
      fullMap := fullMap.insert cd.name fs
    if full.size == before then break
  let fullOf (n : String) := fullMap[n]?.getD []
  for cd in cdefs do
    for (f, _, _, _) in fullOf cd.name do
      if (henv.supers cd.name).any (declaresBase · f) then
        throw s!"{cd.pos.show}: '{f}' is both a field and a method of {cd.name}"
  -- the methods
  let mut expanded : Array STop := #[]
  let mut abstracts : Array (String × String) := #[]
  let mut overridePairs : Array (Pos × String × String) := #[]
  let mut implChecks : Array (Pos × String × String × String) := #[]
  -- constructor functions (#11): `K<constructor>(ps) := c:` and its items
  let ctorOf (t : STop) :
      Option (Pos × String × List SParam × List TParam × List String × String × List SExpr) :=
    match t with
    | .fn p k ps tps effs _ (.block _ items) =>
      match effs.find? (·.startsWith "$constructor:") with
      | some e => some (p, k, ps, tps, effs.filter (· != e), (e.drop "$constructor:".length).toString, items)
      | none => none
    | _ => none
  let ctors := allTops0.filterMap ctorOf
  for t in allTops0 do
    match t with
    | .classDef .. => pure ()
    | t => if (ctorOf t).isNone then expanded := expanded.push t
  let ctorTargs : List (String × List STy) := allTops0.filterMap fun
    | t@(.fn _ k _ _ _ (.app _ ts) _) => if (ctorOf t).isSome then some (k, ts) else none
    | _ => none
  expanded := expanded ++
    (← expandCtors ctors cdef? fullOf (fun c => henv.supers c) (fun k => (ctorTargs.lookup k).getD [])
      (allTops0.filterMap fun t => match t, ctorOf t with
        | .fn _ k _ _ _ (.app _ ts) _, some _ => some (k, ts)
        | .fn _ k _ _ _ _ _, some _ => some (k, [])
        | _, _ => none)).toArray
  for cd in cdefs do
    let n := cd.name
    let fs := fullOf n
    expanded := expanded.push (.const cd.pos n none (.structDef cd.pos cd.tps fs))
    let selfTy : STy := if cd.tps.isEmpty then .name n else .app n (cd.tps.map fun tp => STy.name tp.name)
    for (m, mi) in cd.methods.zip (List.range cd.methods.length) do
      match m with
      | .fn mp mn ps mtps effs ret body =>
        if fs.any (·.1 == methodBase mn) then throw s!"{mp.show}: '{methodBase mn}' is both a field and a method of {n}"
        if mn != "$block" && (cd.methods.take mi).any (fun | .fn _ x .. => x == mn | _ => false) then
          throw s!"{mp.show}: {n} defines {mn} twice with the same parameters"
        if ps.any (·.name == "Self") then throw s!"{mp.show}: a method parameter cannot be called Self"
        if builtins.contains (methodBase mn) || softBuiltins.contains (methodBase mn) then throw s!"{mp.show}: a method cannot be called {methodBase mn}, the name of a built-in function"
        -- (a copy of an interface's default: as in the interface, #53)
        let scope := (copyScope? effs).getD n
        for prm in ps do
          if (fullOf scope).any (·.1 == prm.name) || (henv.supers scope).any (declaresBase · prm.name) then
            throw s!"{mp.show}: parameter '{prm.name}' of {mn} is already a field or method of {scope}; Verse does not allow shadowing"
        -- a class's `block:` clauses: run at construction, after those of the
        -- classes above it, so never overridden
        -- overriding (Book of Verse ch. 10: `M<override>`, the same signature)
        let isOverride := effs.contains "override"
        -- `(q:)M`: implements slot q of M (#70), q the interface that
        -- introduces M
        let qual? : Option (String × String) :=
          if mn.startsWith "(" then match (mn.drop 1).toString.splitOn ":)" with
            | [q, m'] => some (q, m')
            | _ => none
          else none
        if let some (q, m') := qual? then
          if !((henv.supers n).drop 1).contains q then
            throw s!"{mp.show}: ({q}:){m'}: {q} is not a class or interface above {n}"
          let roots := henv.rootsOf (declares · m') q
          let qualify := " or ".intercalate (roots.map fun r => s!"({r}:)")
          if roots.isEmpty then throw s!"{mp.show}: ({q}:){m'}: {q} has no method {m'}"
          if !declares q m' then
            throw s!"{mp.show}: ({q}:){m'}: {q} does not declare {m'} itself; qualify it with {qualify}"
          if roots != [q] then
            throw s!"{mp.show}: ({q}:){m'}: {q}'s {m'} overrides another; qualify it with the interface that introduces {m'}, {qualify}"
          if !isOverride then throw s!"{mp.show}: ({q}:){m'} must be marked <override>"
          if effs.contains "$abstract" then throw s!"{mp.show}: ({q}:){m'} needs a body"
          if cd.methods.any (fun | .fn _ x .. => x == m' | _ => false) then
            throw s!"{mp.show}: {n} implements {m'} both plainly and as ({q}:){m'}: give one or the other"
        -- what the method overrides: the declarations above it in its slots
        -- (for `(q:)m'`, those below q, and the `(q:)m'` above), and for a
        -- plain one the qualified implementations above too
        let ups1 := (henv.supers n).drop 1
        let overridden : List (String × String) :=
          if mn == "$block" then [] else match qual? with
          | some (q, m') =>
            (ups1.filter fun e => declares e m' && henv.isSub e q).map (·, m') ++
              (ups1.filter (declares · mn)).map (·, mn)
          | none =>
            (ups1.filter (declares · mn)).map (·, mn) ++
              ups1.flatMap fun e => (henv.rootsOf (declares · mn) n).filterMap fun r =>
                if declares e s!"({r}:){mn}" then some (e, s!"({r}:){mn}") else none
        match overridden with
        | [] =>
          if isOverride then
            if (henv.supers n).any (fun e => ((cdef? e).map fun ed => ed.methods.any fun
                | .fn _ x .. => x.startsWith s!"{mn}$ov" | _ => false).getD false) then
              throw s!"{mp.show}: {mn}<override> has the parameters of no overload of {mn} above {n}"
            throw s!"{mp.show}: {mn}<override> does not override an inherited method"
        | qs@((q, _) :: _) =>
          if !isOverride then throw s!"{mp.show}: {mn} is inherited from {q}: mark it {mn}<override> to override it"
          for (q, x) in qs do
            match (cdef? q).bind (methodNamed · x) with
            | some (.fn _ _ _ qtps qeffs _ _) =>
              -- (a copy is exempt, and a copy's `<final>` is its interface's,
              -- which the message names)
              if qeffs.contains "final" && !qeffs.contains "$copy" && !effs.contains "$copy" then
                throw s!"{mp.show}: {q}.{x} is <final>: it cannot be overridden"
              -- (a method with its own type parameters overrides one with as
              -- many, compared up to their names below)
              if qtps.length != mtps.length then
                throw s!"{mp.show}: {mn} has {mtps.length} type parameter(s) of its own, and {q}.{x}, which it overrides, {qtps.length}"
            | _ => pure ()
            overridePairs := overridePairs.push (mp, s!"{n}.{mn}", s!"{q}.{x}")
        let body ← if effs.contains "$abstract" then do
            if !cd.isIface && !cd.specs.contains "abstract" then
              throw s!"{mp.show}: {mn} has no body: give it one, or make {n} <abstract>"
            abstracts := abstracts.push (n, mn)
            pure (SExpr.app mp (.ident mp "Err") [] false)   -- never called
          else pure body
        expanded := expanded.push
          (.fn mp s!"{n}.{mn}" ({ name := "Self", ty := selfTy } :: ps) (cd.tps ++ mtps) effs ret body)
      | _ => pure ()
  -- a concrete class implements every method it has, each unambiguously
  for cd in cdefs do
    let i := henv.info cd.name
    if i.isIface || i.isAbstract then continue
    let ups := henv.supers cd.name
    let names := (ups.flatMap fun u => ((cdef? u).map (·.methods)).getD [] |>.filterMap fun
      | .fn _ x .. => some x
      | _ => none).eraseDups
    -- (a `block:` is not a method: each class runs its own; a qualified
    -- `(q:)M` implements q's M, below)
    for mn in names.filter (fun x => x != "$block" && !x.startsWith "(") do
      let decls := ups.filter (declares · mn)
      -- each slot (#70): its implementation, as `Ctx.implFor?` chooses at a
      -- call, satisfies every declaration in the slot
      let roots := henv.rootsOf (declares · mn) cd.name
      let implAt (r e : String) : Option String :=
        if hasBody e s!"({r}:){mn}" then some s!"{e}.({r}:){mn}"
        else if hasBody e mn then some s!"{e}.{mn}" else none
      let clsOf (f : String) : String := (f.splitOn ".").head!
      let mut chosen : List String := []
      for r in roots do
        match henv.slotImpls (implAt r) ups r with
        | [] => throw s!"{cd.pos.show}: {cd.name} must implement {mn} (declared abstract in {r})"
        | f :: g :: _ =>
          throw s!"{cd.pos.show}: {cd.name} inherits {mn} from both {clsOf f} and {clsOf g}: override it in {cd.name}"
        | [f] =>
          chosen := chosen ++ [f]
          for q in decls.filter (henv.isSub · r) do
            if f != s!"{q}.{mn}" then implChecks := implChecks.push (cd.pos, cd.name, f, s!"{q}.{mn}")
      -- without a qualified implementation, one implementation for all slots
      let qualified := ups.any fun e => roots.any fun r => declares e s!"({r}:){mn}"
      match chosen.eraseDups with
      | f :: g :: _ =>
        if !qualified then
          throw s!"{cd.pos.show}: {cd.name} inherits {mn} from both {clsOf f} and {clsOf g}: override it in {cd.name}"
      | _ => pure ()
  let allTops := expanded.toList
  -- the type definitions: `name := struct …` and `name := enum …`
  let isTypeDef : STop → Bool
    | .const _ _ none (.structDef ..) | .const _ _ none (.enumDef ..) | .const _ _ none (.refineDef ..) => true
    | _ => false
  let tops := allTops.filter (!isTypeDef ·)
  let varFields : List (String × String) := cdefs.flatMap fun cd =>
    (fullOf cd.name).filterMap fun (f, _, _, isVar) => if isVar then some (cd.name, f) else none
  let uniques : List String := (cdefs.filter (·.specs.contains "unique")).map (·.name)
  let mut env : TyEnv := { classes := henv.classes, cinfo := henv.cinfo, cinfoMap := henv.cinfoMap,
                           classIx := henv.classes.zipIdx.foldl (fun m (n, i) => m.insert n i) {},
                           belowReady := true,
                           supersMap := henv.classes.foldl (fun m d => m.insert d (henv.supers d)) {},
                           belowMap := henv.classes.foldl (fun m d =>
                             let i := henv.info d
                             if i.isIface || i.isAbstract then m else
                             (henv.supers d).foldl (fun m T => m.insert T ((m[T]?.getD []) ++ [d])) m) {},
                           abstracts := abstracts.toList, fnRequests := opts.fnRequests, methodRequests := opts.methodRequests,
                           castRequests := opts.castRequests, loopRequests := opts.loopRequests }
  env := { env with varFields := varFields, uniques := uniques,
                    overriders := (overridePairs.toList.map fun (_, dm, _) => (dm.splitOn ".").headD "") ++
                      (implChecks.toList.map fun (_, _, impl, _) => (impl.splitOn ".").headD "") ++
                      -- (#250: and the targets of refining casts, whose own
                      -- pins relate their type arguments to the object's, as
                      -- the dispatch to the branch refines by: also one that
                      -- only inherits and gives its parent a compound of its
                      -- own, `c1(t) := class(c0([]t))`, #243, #351)
                      (opts.castRequests.map (·.target)) ++
                      (opts.loopRequests.filterMap fun lift =>
                        if (lift.name.splitOn "$dispatchDefaultsSpawn").length > 1 then
                          some ((lift.name.splitOn ".").headD "") else none) }
  -- the class whose code each inherited field default is (#39): the nearest
  -- one, the class's own first, that gives the field a default itself
  let homeOf (c f : String) : String :=
    ((henv.supers c).find? fun x =>
      ((cdef? x).map fun xd => xd.fields.any fun (g, _, d, _) => g == f && d.isSome).getD false).getD c
  env := { env with defaultHome := cdefs.flatMap fun cd =>
    (fullOf cd.name).filterMap fun (f, _, d, _) => d.map fun _ => ((cd.name, f), homeOf cd.name f) }
  for t in allTops do
    match t with
    | .const _ n none (.enumDef _ vals isOpen) =>
      env := { env with enums := env.enums ++ [(n, vals)],
                        openEnums := if isOpen then env.openEnums ++ [n] else env.openEnums }
    | .const _ n none (.structDef _ _ _) => env := { env with structs := env.structs ++ [(n, [])] }
    | .const p n none (.refineDef _ v sty conds) =>
      -- a refinement type (#136)
      let (base, _) ← (resolveTy env p sty).run {}
      env := { env with refines := env.refines ++ [(n, base, ← refineConds p v base conds)] }
    | _ => pure ()
  -- the type parameters of parametric structs
  for t in allTops do
    match t with
    | .const _ n none (.structDef _ tps@(_ :: _) _) =>
      env := { env with sparams := env.sparams ++ [(n, ← checkTParams env tps)] }
    | _ => pure ()
  let shell := env
  let mut structs := #[]
  for t in allTops do
    match t with
    | .const p n none (.structDef _ _ fs) =>
      let senv := { shell with tvars := (shell.sparams.lookup n).getD [] |>.map fun (v, c) => (v, Ty.param v c) }
      let fields ← fs.mapM fun (f, sty, d, _) => do
        let (ty, _) ← (resolveTy senv p sty).run {}
        pure (f, ty, d)
      structs := structs.push (n, fields)
    | _ => pure ()
  env := { env with structs := structs.toList }
  -- the type arguments of each class's parametric superclass (#39)
  let mut pargs : Array (String × List Ty) := #[]
  for cd in cdefs do
    if let some q := (henv.info cd.name).parent then
      let qargs := ((cd.parents.zip cd.parentArgs).lookup q).getD []
      if !qargs.isEmpty then
        let cenv := { env with tvars := ((env.sparams.lookup cd.name).getD []).map fun (v, c) => (v, Ty.param v c) }
        let tys ← qargs.mapM fun sty => do
          let (ty, _) ← (resolveTy cenv cd.pos sty).run {}
          pure ty
        -- a type argument the parent requires to be comparable is
        for (ty, (v, needComp)) in tys.zip ((env.sparams.lookup q).getD []) do
          if needComp && !ty.comparable env then
            throw s!"{cd.pos.show}: {cd.name} gives {q} the type argument {ty.show} for {v}, which must be comparable"
        pargs := pargs.push (cd.name, tys)
  env := { env with pargs := pargs.toList }
  -- the type arguments of each parametric interface a class or interface
  -- lists as a parent (#53), and none for an interface a class with type
  -- parameters lists without them (#276): the class's root then gives none
  let mut iargs : Array ((String × String) × List Ty) := #[]
  for cd in cdefs do
    for (q, qargs) in cd.parents.zip cd.parentArgs do
      if (henv.info q).isIface && qargs.isEmpty && !((env.sparams.lookup cd.name).getD []).isEmpty then
        iargs := iargs.push ((cd.name, q), [])
      if (henv.info q).isIface && !qargs.isEmpty then
        let cenv := { env with tvars := ((env.sparams.lookup cd.name).getD []).map fun (v, c) => (v, Ty.param v c) }
        let tys ← qargs.mapM fun sty => do
          let (ty, _) ← (resolveTy cenv cd.pos sty).run {}
          pure ty
        for (ty, (v, needComp)) in tys.zip ((env.sparams.lookup q).getD []) do
          if needComp && !ty.comparable env then
            throw s!"{cd.pos.show}: {cd.name} gives {q} the type argument {ty.show} for {v}, which must be comparable"
        iargs := iargs.push ((cd.name, q), tys)
  env := { env with iargs := iargs.toList }
  -- a class overrides a method only if its Verse Core type arguments are its
  -- own distinct type parameters, as many as the declaring class's: code
  -- generic over that class can then call its implementation (it could not
  -- give it a type argument it fixes, nor one it adds)
  let core (c : String) : List Ty :=
    env.coreArgs c (((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k)
  -- a class below an interface has as its Verse Core type arguments first
  -- those it gives the interface: references to the interface have those,
  -- and dispatch and field reads through them recover the class's (#53);
  -- its other type parameters come after, held by its objects in hidden
  -- fields, and a dispatch from the interface opens them, as for a class
  -- whose parent's type arguments do not give them (#209, #276)
  let mut viewed : List String := []
  let mut witnessNeeds : List String := []
  for cd in cdefs do
    if !cd.isIface then
      -- (an interface reached through two parents at different type
      -- arguments: the class would implement two instances of it, #53)
      -- (compared as resolved types: equal ones may be written differently)
      -- (each listing: `iargs` keeps one entry per listed parent, also one
      -- listed twice)
      let insts := env.iargs.flatMap fun ((c, q), tys) =>
        if c == cd.name && (env.info q).isIface then env.ifaceInstances q tys else []
      let sh (ts : List Ty) : String := ", ".intercalate (ts.map Ty.show)
      for (i, ia) in insts do
        if let some (_, ib) := insts.find? fun (j, jb) => j == i && jb != ia then
          throw s!"{cd.pos.show}: {cd.name} implements {i} at two instances, {i}({sh ia}) and {i}({sh ib}), through the interfaces it lists: a class implements one instance of an interface (#53)"
      let ps := ((env.sparams.lookup cd.name).getD []).map fun (v, k) => Ty.param v k
      for i in (env.supers cd.name).filter (env.info · |>.isIface) do
        let ia := env.upArgs cd.name ps i
        -- (at the interface's Verse Core type arguments, which also hold
        -- those it gives its own parents, `c2(t)`'s `[]t, t`)
        if !((env.coreArgs i ia).isPrefixOf (core cd.name)) then
          let showArgs (ts : List Ty) : String := if ts.isEmpty then "none" else ", ".intercalate (ts.map Ty.show)
          -- (and, where they differ, as the interface holds them, #53)
          let ica := env.coreArgs i ia
          let gives := if ica == ia then showArgs ia else s!"{showArgs ia} (which {i} holds as {showArgs ica})"
          -- (#351) references to the interface go through views, each class
          -- below with its own; its fields would be at other places in its
          -- classes, which no view gives
          -- (a dispatch through a view reads all of the class's type
          -- arguments from its hidden fields, which a class without a class
          -- parent has for all of them; one with one, which adds the
          -- interface, has them for all only when asked, and the program is
          -- elaborated again, `Options.witnessAll`)
          if let some q := (env.info cd.name).parent then
            if !env.isSub q i && !opts.witnessAll.contains cd.name && !witnessNeeds.contains cd.name then
              witnessNeeds := witnessNeeds ++ [cd.name]
          viewed := viewed ++ [i]
  for lift in opts.loopRequests do
    if defaultBridge lift.name || spawnAdapter lift.name then
      let cls := (lift.name.splitOn ".").headD ""
      let needed := lift.specs.filterMap fun flag =>
        if flag.startsWith "$selfTp:" then some (flag.drop 8).toString else none
      if needed.any (fun n => (env.witnessField? cls n).isNone) &&
          !opts.witnessAll.contains cls && !witnessNeeds.contains cls then
        witnessNeeds := witnessNeeds ++ [cls]
  if !witnessNeeds.isEmpty then
    return { prog := default, sigs := { fns := [] }, slotTys := [], witnessNeeds }
  -- (and the interfaces above them, which see their classes through a
  -- prefix of what they do)
  env := { env with viewed := (viewed ++ viewed.flatMap fun i => (env.supers i).filter (env.info · |>.isIface)).eraseDups }
  for (mp, dm, qm) in overridePairs do
    let d := (dm.splitOn ".").head!
    let q := (qm.splitOn ".").head!
    let mn := (dm.splitOn ".").getLast!
    let (cd', cq) := (core d, core q)
    -- (not through views, #351: a dispatch through one opens the class's
    -- type arguments, related to the interface's by its view, which may
    -- have more, `q(t) := class(p(t), keyed(string, t))`)
    if !env.viewed.contains q && !env.sameCorePinned d q then
      if ((env.sparams.lookup d).getD []).isEmpty then
        throw s!"{mp.show}: {d} has more Verse Core type arguments than {q} (a class between them has type parameters of its own), so it cannot override {mn} yet: code generic over {q} could not give them (#39)"
      throw s!"{mp.show}: {d} has type parameters that {q} does not have and that the type arguments it gives {q} do not determine, so it cannot override {mn}: code generic over {q} could not give them (#39, #209)"
    -- (its Verse Core type arguments are {q}'s, except where it fixes them
    -- or relates them to each other: dispatch is then typed under the
    -- refinement its pins give, #142, #209)
  -- the classes whose implementations fix type arguments their declaring
  -- class leaves open, and the classes below them, are dispatched to under
  -- a refinement, so Verse Core records their pins (#142)
  -- (the pins of the classes in override pairs, once, #238; not of every
  -- class, as a class whose Verse Core type would contain itself is refused
  -- only below, and computing its pins would not end)
  let pinClasses := (overridePairs.toList.flatMap fun (_, dm, qm) =>
      [(dm.splitOn ".").head!, (qm.splitOn ".").head!]).eraseDups
  env := { env with pinsMap := pinClasses.foldl (fun m d => m.insert d (env.pinsOf d)) {} }
  let fixes (e q : String) : Bool :=
    ((env.pinsOf q).zip (env.pinsOf e)).any (fun (a, b) => a != b) || (env.pinsOf e).length > (env.pinsOf q).length
  let headOf (f : String) : String := (f.splitOn ".").head!
  let fixers := (overridePairs.toList.filterMap fun (_, dm, qm) =>
      if fixes (headOf dm) (headOf qm) then some (headOf dm) else none) ++
    (implChecks.toList.filterMap fun (_, _, impl, decl) =>
      if fixes (headOf impl) (headOf decl) then some (headOf impl) else none)
  -- (and the classes that fix an interface's type arguments, below an
  -- interface whose fields sit at different places in its classes: its
  -- fields are reached through accessors, under the refinement, #157; so
  -- is a field such a class types otherwise than a class or interface
  -- above it, taking it from another interface, #205)
  let mut fieldAcc : Array (String × String) := #[]
  let mut accFixers : Array String := #[]
  for i in env.classes do
    let ds := env.concreteBelow i
    for (f, _, _) in env.fields i do
      let pos := ds.map fun d => ((fieldIndex (env.fields d) f).map (·.1)).getD 0
      let moved := (env.info i).isIface && !pos.all (· == pos.headD 0)
      let τi := env.coreFieldTy i f
      -- (a read that tests the class first needs an accessor for each class
      -- that fixes type arguments, also one that types the field as `i`)
      let retyped := ds.any fun d => env.coreFieldTy d f != τi
      for d in ds do
        if (moved || retyped) && fixes d i && env.sameCorePinned d i &&
            !fieldAcc.contains (d, f) then
          fieldAcc := fieldAcc.push (d, f)
          accFixers := accFixers.push d
        -- (#351: through views, every class's, a read of a dispatch through
        -- one, `Typed.dispatch_view`, as a method's call is)
        else if env.viewed.contains i && !fieldAcc.contains (d, f) then
          fieldAcc := fieldAcc.push (d, f)
  -- (and a concrete class with a class below it that types one of its
  -- fields otherwise: a read that tests for it reaches the field through
  -- its accessor, whose receiver is of exactly its class, as a temporary
  -- of its type also holds the classes below it, #205)
  for d in env.classes.filter (fun d => let i := env.info d; !i.isIface && !i.isAbstract) do
    for (f, _, _) in env.fields d do
      let τ := env.coreFieldTy d f
      if (env.concreteBelow d).any (fun d' => d' != d && env.coreFieldTy d' f != τ) &&
          !fieldAcc.contains (d, f) then
        fieldAcc := fieldAcc.push (d, f)
  -- (#243) and the classes refining casts test for, by their target
  -- (whose pins the dispatch to the cast's branch refines by)
  let spawnFixers := opts.loopRequests.filterMap fun lift =>
    if (lift.name.splitOn "$dispatchDefaultsSpawn").length > 1 then
      some ((lift.name.splitOn ".").headD "") else none
  let fixers := fixers ++ accFixers.toList ++ env.castRequests.map (·.target) ++ spawnFixers
  env := { env with pinned := env.classes.filter fun d => fixers.any fun f => d == f || (env.supers d).contains f,
                    fieldAcc := fieldAcc.toList }
  -- (#157) a hidden class below each generic class or interface whose
  -- concrete classes all fix some of its type arguments: a variable of its
  -- type at other type arguments starts as one. It has the class's fields
  -- (a class's include its interfaces'), and the program never makes one
  -- (an interface's placeholder is laid out for reads through `n` and the
  -- interfaces above it: each of `n`'s fields, inherited ones too, where
  -- every class below `n` has it, when they agree, else after those, as a
  -- read then tests the class first; padding between. A read through an
  -- interface `T` above `n` goes straight to the field only when every class
  -- below `T` has it at one place, and those include `n`'s, so it is the
  -- place here too. A placeholder needs a concrete class below, and no two
  -- fields share a place in one)
  let ifaceLayout (n : String) : List (String × Ty × Option SExpr) := Id.run do
    let ds := env.concreteBelow n
    let mut fixed : List (Nat × String × Ty) := []
    let mut free : List (String × Ty) := []
    for (f, t, _) in env.fields n do
      let pos := ds.map fun d => ((fieldIndex (env.fields d) f).map (·.1)).getD 0
      match pos.head? with
      | some p0 => if pos.all (· == p0) then fixed := fixed ++ [(p0, f, t)] else free := free ++ [(f, t)]
      | none => free := free ++ [(f, t)]
    let size := (fixed.map (·.1 + 1)).foldl max 0
    let laid := (List.range size).map fun k => match fixed.find? (·.1 == k) with
      | some (_, f, t) => (f, t, (none : Option SExpr))
      | none => (s!"$pad{k}", Ty.void, none)
    return laid ++ free.map fun (f, t) => (f, t, none)
  let coreLen (c : String) : Nat :=
    (env.coreArgs c (((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k)).length
  let needsPh (n : String) : Bool :=
    env.isRefClass n &&
    (((env.sparams.lookup n).isSome &&
        (env.concreteBelow n).all (fun d => env.pinned.contains d && (env.corePins d).any Option.isSome)) ||
      -- (or a class below with type parameters a dispatch on `n` opens,
      -- #209: an object of it needs more type arguments than `n`'s)
      (env.concreteBelow n).any fun d => env.pinned.contains d && coreLen d > coreLen n)
  for n in env.classes.filter needsPh do
    let h := s!"{n}$placeholder"
    let i := env.info n
    let ps := (env.sparams.lookup n).getD []
    let own := ps.map fun (v, c) => Ty.param v c
    env := { env with
      classes := env.classes ++ [h],
      structs := env.structs ++ [(h, if i.isIface then ifaceLayout n else (env.structs.lookup n).getD [])],
      sparams := env.sparams ++ [(h, ps)],
      cinfo := env.cinfo ++ [(h, { parent := if i.isIface then none else some n,
                                   ifaces := if i.isIface then [n] else [], isAbstract := true })],
      pargs := if i.isIface then env.pargs else env.pargs ++ [(h, own)],
      iargs := if i.isIface then env.iargs ++ [((h, n), own)] else env.iargs,
      phs := env.phs ++ [h],
      -- (below a class that records pins, it records the same)
      pinned := if env.pinned.contains n then env.pinned ++ [h] else env.pinned }
  -- (their superclasses too, as every class's, so that a test of whether
  -- a placeholder is below a class does not walk the chain each time:
  -- `refTags` asks that of each at each conversion of a class type)
  env := { env with supersMap := env.phs.foldl (fun m h => m.insert h (env.supersWalk h)) env.supersMap }
  env := { env with protos := env.makeProtos }
  if let some n := env.recursiveStruct? then
    if env.classes.contains n then
      throw s!"the Verse Core type of class {n} would contain itself, through its type arguments (#63)"
    throw s!"struct {n} contains itself (recursive struct types are not supported)"
  -- map keys in field types, now that every struct's fields are known
  -- (a key type can be a struct that holds a class)
  for (sn, fs) in env.structs do
    for (f, ft, _) in fs do
      if !ft.mapKeysOK env then
        throw s!"field '{f}' of {sn}: a map key must be comparable, and {ft.show} has a key that is not"
  -- overloading (#74): functions of one name, each renamed `F$ovN`; a call
  -- takes the one its arguments fit (`elabApp`), and no call fits two
  let fnNames := tops.filterMap fun | .fn _ n .. => some n | _ => none
  let ovNames := (fnNames.filter fun n => (fnNames.filter (· == n)).length > 1 && !n.contains '.').eraseDups
  let mut ovMap : List (String × List String) := []
  let mut renamed : Array STop := #[]
  for t in tops do
    match t with
    | .fn p n ps tps effs ret body =>
      if ovNames.contains n then
        if n == "Main" then throw s!"{p.show}: Main cannot be overloaded"
        if builtins.contains n then throw s!"{p.show}: '{n}' is a built-in function"
        if tops.any (fun | .const _ m .. | .classDef _ m .. => m == n | _ => false) ||
            env.classes.contains n || (env.structs.lookup n).isSome || (env.enums.lookup n).isSome then
          throw s!"{p.show}: '{n}' is defined twice (only functions can be overloaded)"
        let prev := (ovMap.lookup n).getD []
        let m := s!"{n}$ov{prev.length}"
        ovMap := (ovMap.filter (·.1 != n)) ++ [(n, prev ++ [m])]
        renamed := renamed.push (.fn p m ps tps effs ret body)
      else renamed := renamed.push t
    | t => renamed := renamed.push t
  let tops := renamed.toList
  env := { env with overloads := ovMap,
                    methodOverloads :=
                      let bases := (mov.map (·.1.2)).eraseDups
                      bases.map fun mn =>
                        let n := (mov.filter (·.1.2 == mn)).foldl (fun acc (_, sigs) => max acc sigs.length) 0
                        (mn, (List.range n).map fun k => s!"{mn}$ov{k}") }
  -- generic functions (those with a `where` clause) are numbered after the
  -- other functions and constants
  let isGeneric : STop → Bool
    | .fn _ _ _ (_ :: _) .. => true
    | _ => false
  let generics := tops.filter isGeneric
  let names := tops.map fun | .fn _ n .. => n | .const _ n .. => n | .classDef _ n .. => n
  let tops := tops.filter (!isGeneric ·)
  for (n, i) in names.zip (List.range names.length) do
    if names.take i |>.contains n then throw s!"'{n}' is defined twice (only functions can be overloaded)"
    if builtins.contains n then throw s!"'{n}' is a built-in function"
  -- A cast discovered before a default helper must acquire the helper
  -- effects once its body is known, before checking the source caller.
  let inferredBridge (n : String) := defaultBridge n || opts.castRequests.any (·.name == n)
  -- a function's parameter and result types
  let fnTypes (env : TyEnv) (p : Pos) (n : String) (ps : List SParam) (effs : List String) (ret : STy) :
      Except String (List Ty × Ty) := do
    if effs.contains "suspends" then
      if effs.contains "decides" then
        throw s!"{p.show}: {n} is both <suspends> and <decides>, which exclude each other"
      if n.endsWith "$init" then
        throw s!"{p.show}: a <suspends> constructor is not supported (#156)"
    let (tys, _) ← ((ps.mapM fun prm => resolveTy env p prm.ty).run {})
    let (rt, _) ← (resolveTy env p ret).run {}
    -- named parameters come last (Book of Verse §8.2)
    let rec namedLast : List SParam → Bool
      | [] => true
      | q :: qs => if q.named then qs.all (·.named) else namedLast qs
    if !namedLast ps then throw s!"{p.show}: in {n}, every parameter after a named one must be named"
    return (tys, rt)
  -- signatures: functions from their annotations, constants from theirs or by inference
  let mut sigs : Array Sig := #[]
  for (top, idx) in tops.zip (List.range tops.length) do
    match top with
    | .fn p n ps _ effs ret _ =>
      let (tys, rt) ← fnTypes env p n ps effs ret
      if (["converges", "computes", "transacts"].filter effs.contains).length > 1 then
        throw s!"{p.show}: {n} has more than one of <converges>, <computes> and <transacts> (they exclude each other)"
      if effs.contains "computes" && ("transacts" :: heapFx).any effs.contains then
        throw s!"{p.show}: <computes> excludes the heap effects (<reads>, <writes>, <allocates>, <transacts>) that {n} also has"
      sigs := sigs.push { idx, name := n, params := tys, ret := rt, decides := effs.contains "decides",
                          suspends := effs.contains "suspends",
                          -- (a `block:`'s effects are inferred below, from none, as a
                          -- constant's: blocks that construct each other's classes)
                          fx := if n.endsWith ".$block" || defaultBridge n || (n.splitOn "$default$").length > 1 then [] else allowedFx effs,
                          isConst := false,
                          named := (ps.filter (·.named)).map fun q => (q.name, q.default),
                          pnames := ps.map (·.name), scope := copyScope? effs }
    | .const p n sty _ =>
      let rt ← match sty with
        | some t => do let (rt, _) ← (resolveTy env p t).run {}; pure rt
        | none => pure .never   -- inferred below
      -- a constant's heap effects are inferred below, from none
      sigs := sigs.push { idx, name := n, params := [], ret := rt, decides := false, isConst := true, fx := [] }
    | .classDef .. => pure ()   -- expanded above
  -- the signatures of the generic functions, over their type parameters
  let mut gsigs : Array Sig := #[]
  for (top, gidx) in generics.zip (List.range generics.length) do
    match top with
    | .fn p n ps tps effs ret _ =>
      if n == "Main" then throw s!"{p.show}: Main cannot be generic"
      let tparams ← checkTParams env tps
      let genv := { env with tvars := tparams.map fun (v, c) => (v, Ty.param v c) }
      let (tys, rt) ← fnTypes genv p n ps effs ret
      if (["converges", "computes", "transacts"].filter effs.contains).length > 1 then
        throw s!"{p.show}: {n} has more than one of <converges>, <computes> and <transacts> (they exclude each other)"
      if effs.contains "computes" && ("transacts" :: heapFx).any effs.contains then
        throw s!"{p.show}: <computes> excludes the heap effects (<reads>, <writes>, <allocates>, <transacts>) that {n} also has"
      -- (#209) a method of a class with type parameters that its parent's
      -- type arguments do not give reads their values from its receiver
      -- (an overriding implementation: what a dispatch that opens them
      -- reaches; the class's other methods are called at known types)
      -- (#250: the function a cast's branch is lifted into, from the object,
      -- the cast's subject, its first parameter)
      let lifted := opts.castRequests.find? (·.name == n)
      let selfTps : List String := if defaultBridge n || spawnAdapter n then
          (effs.filterMap fun e => if e.startsWith "$selfTp:" then some (e.drop 8).toString else none).filter
            (fun v => tparams.any (·.1 == v))
        else if let some l := lifted then
          (l.opened.map (·.1)).filter fun v => tparams.any (·.1 == v) else
        match n.splitOn "." with
        | [c, m] =>
          -- Bound-method value adapters and registered resume methods can
          -- open receiver parameters absent from their value signatures.
          let valueCall := m == "$call" || m.startsWith "$call:"
          let resumeCall := opts.loopRequests.any (fun l => l.resumes.any (·.name == n))
          if effs.contains "override" && env.classes.contains c && env.isRefClass c &&
              (!m.startsWith "$" || valueCall || resumeCall) &&
              (match tys.head? with | some (.struct c' _) => c' == c | _ => false) then
            -- (#351: below an interface referred to through views, every
            -- type parameter, which a dispatch through a view may open)
            (if env.viewed.any (env.isSub c ·) then ((env.sparams.lookup c).getD []).map (·.1)
             else env.addedParams c).filter fun v => tparams.any (·.1 == v) && (env.witnessField? c v).isSome
          else []
        | _ => []
      -- generic functions come after the others
      gsigs := gsigs.push { idx := tops.length + gidx, name := n, params := tys, ret := rt, selfTps,
                            decides := effs.contains "decides", isConst := false,
                            suspends := effs.contains "suspends",
                            -- (a parametric class's `block:`: inferred from none, #41)
                            fx := if n.endsWith ".$block" || defaultBridge n then [] else allowedFx effs,
                            tparams,
                            named := (ps.filter (·.named)).map fun q => (q.name, q.default),
                            pnames := ps.map (·.name), scope := copyScope? effs }
    | _ => pure ()
  let mkSigProg (sigs : Array Sig) : Prog :=
    { fns := (sigs ++ gsigs).toList.map fun s =>
        { name := s.name, arity := s.params.length + s.ndicts, nslots := 0,
          decides := s.decides, writes := s.fx.contains "writes", body := .lit .void },
      main := 0 }
  -- infer the types of unannotated constants: in order, in rounds, so that a
  -- constant may use one defined after it (until a round makes no progress)
  let unannotated := (tops.zip (List.range tops.length)).filter fun
    | (.const _ _ none _, _) => true
    | _ => false
  let mut todo := unannotated
  for _ in [0:unannotated.length + 1] do
    let mut left := #[]
    for (top, idx) in todo do
      match top with
      | .const _ _ _ body =>
        let ctx : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env }
        match (elabE ctx body none).run { env } with
        | .ok (r, _) =>
          if r.ty == .never then left := left.push (top, idx)
          else sigs := sigs.set! idx { sigs[idx]! with ret := r.ty }
        | .error _ => left := left.push (top, idx)
      | _ => pure ()
    if left.size == todo.length then break
    todo := left.toList
  -- the first constant still unknown gives its own error
  for (top, _) in todo do
    match top with
    | .const p n _ body =>
      let ctx : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env }
      let (r, _) ← (elabE ctx body none).run { env }
      if r.ty == .never then throw s!"{p.show}: cannot infer the type of '{n}'"
    | _ => pure ()
  -- the heap effects of a constant are those of its initialiser (#35), which
  -- runs at each use: in rounds, from none, since constants use each other
  for _ in [0:tops.length + generics.length + 1] do
    let mut changed := false
    for (top, idx) in tops.zip (List.range tops.length) do
      match top with
      | .const _ _ _ body =>
        let ctx : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env }
        match elabBodyOv ctx body (some sigs[idx]!.ret) { env } with
        | .ok (_, st) =>
          let fx := heapFx.filter fun k => st.fx.any (·.1 == k)
          if fx != sigs[idx]!.fx then
            sigs := sigs.set! idx { sigs[idx]! with fx }
            changed := true
        | .error _ => pure ()
      -- a class's `block:` clauses have the effects of their code, and so
      -- does a default an overloaded constructor fills in (#99)
      | .fn p n ps _ _ _ body =>
        if (n.splitOn "$default$").length > 1 then
          let ctx : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env }
          match elabBodyOv ctx body (some sigs[idx]!.ret) { env } with
          | .ok (_, st) =>
            let fx := heapFx.filter fun k => st.fx.any (·.1 == k)
            if fx != sigs[idx]!.fx then
              sigs := sigs.set! idx { sigs[idx]! with fx }
              changed := true
          | .error _ => pure ()
        else if n.endsWith ".$block" || inferredBridge n then
          let s := sigs[idx]!
          let locals := (ps.zip (List.range ps.length)).zip s.params |>.map fun ((prm, i), t) =>
            ({ name := prm.name, slot := i, ty := t, mutable := false } : Local)
          let base : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env,
                              locals := locals.reverse, retTy := s.ret, canFail := s.decides, suspends := s.suspends, fnFx := s.fx }
          let ctx ← functionBodyCtx opts base p n s.tparams s.scope
          match elabBodyOv ctx body (some s.ret) { env, nslots := ps.length, slotTys := s.params.toArray, frameSlots := ctx.locals.filterMap fun l => l.storage.map (l.slot, ·) } with
          | .ok (_, st) =>
            let fx := heapFx.filter fun k => st.fx.any (·.1 == k) ||
              (opts.castRequests.any (·.name == n) && s.fx.contains k)
            if fx != s.fx then
              sigs := sigs.set! idx { s with fx }
              changed := true
          | .error _ => pure ()
      | _ => pure ()
    -- and so do those of a parametric class, generic (#39)
    for (top, gi) in generics.zip (List.range generics.length) do
      match top with
      | .fn p n ps _ _ _ body =>
        if n.endsWith ".$block" || inferredBridge n then
          let g := gsigs[gi]!
          let locals := (ps.zip (List.range ps.length)).zip g.params |>.map fun ((prm, i), t) =>
            ({ name := prm.name, slot := i, ty := t, mutable := false } : Local)
          let dictTps := g.tparams.filter (fun (v, _) => !g.selfTps.contains v) ++
            g.tparams.filter (fun (v, _) => g.selfTps.contains v)
          let hidden := dictTps.map fun (v, c) => Ty.param v c
          let lifted := opts.castRequests.find? (·.name == n)
          let selfField (v : String) := match lifted with
            | some l => (l.opened.lookup v).bind (env.witnessField? l.target ·)
            | none => env.witnessField? ((n.splitOn ".").headD "") v
          let genv := { env with tvars := g.tparams.map fun (v, c) => (v, Ty.param v c), dictOrder := dictTps.map (·.1), selfWitness := g.selfTps.map fun v => (v, (selfField v).getD 0) }
          let base : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := genv,
                              locals := locals.reverse, retTy := g.ret, canFail := g.decides, suspends := g.suspends,
                              dictBase := ps.length, dictVars := dictTps.map (·.1), fnFx := g.fx }
          let ctx ← functionBodyCtx opts base p n g.tparams g.scope
          match elabBodyOv ctx body (some g.ret)
              { env := genv, nslots := ps.length + hidden.length, slotTys := (g.params ++ hidden).toArray, frameSlots := ctx.locals.filterMap fun l => l.storage.map (l.slot, ·) } with
          | .ok (_, st) =>
            let fx := heapFx.filter fun k => st.fx.any (·.1 == k) ||
              (opts.castRequests.any (·.name == n) && g.fx.contains k)
            if fx != g.fx then
              gsigs := gsigs.set! gi { g with fx }
              changed := true
          | .error _ => pure ()
      | _ => pure ()
    if !changed then break
  let sigProg := mkSigProg sigs
  let allSigs := sigs.toList ++ gsigs.toList
  -- overloads take parameters no call fits both of (Book of Verse ch. 6)
  let sigNamed (s : Sig) : List (String × Bool × Ty) :=
    let npos := s.params.length - s.named.length
    (s.named.zip (s.params.drop npos)).map fun ((n, d), t) => (n, d.isSome, t)
  let sigsDistinct (sa sb : Sig) : Bool :=
    let pa := sa.params.take (sa.params.length - sa.named.length)
    let pb := sb.params.take (sb.params.length - sb.named.length)
    env.paramsDistinct pa pb || env.namedDistinct (sigNamed sa) (sigNamed sb)
  for (n, ms) in env.overloads do
    for (a, i) in ms.zip (List.range ms.length) do
      for b in ms.take i do
        match allSigs.find? (·.name == a), allSigs.find? (·.name == b) with
        | some sa, some sb =>
          if !sigsDistinct sa sb then
            let pos := ((tops ++ generics).findSome? fun | .fn q m .. => if m == a then some q else none | _ => none).getD { line := 0, col := 0 }
            let sh (s : Sig) := ", ".intercalate ((s.params.zip (List.range s.params.length)).map fun (t, i) =>
              let npos := s.params.length - s.named.length
              if i < npos then t.show else s!"?{((s.named.drop (i - npos)).head?.map (·.1)).getD "?"}:{t.show}")
            throw s!"{pos.show}: {n} is defined twice with parameters a call cannot tell apart, ({sh sb}) and ({sh sa}): overloads must take disjoint types"
        | _, _ => pure ()
  -- the overloads of a method a class sees take parameters no call fits two
  -- of (#106: a subclass's new overload too; an override has its method's)
  for c in env.classes do
    for (mn, ms) in env.methodOverloads do
      let vis : List (String × Sig) := ms.filterMap fun o =>
        ((env.supers c).find? fun e => allSigs.any (·.name == s!"{e}.{o}")).bind fun e =>
          (allSigs.find? (·.name == s!"{e}.{o}")).map fun sg => (s!"{e}.{o}", { sg with params := sg.params.drop 1 })
      for ((a, sa), i) in vis.zip (List.range vis.length) do
        for (b, sb) in vis.take i do
          if !sigsDistinct sa sb then
            let sh (s : Sig) := ", ".intercalate (s.params.map Ty.show)
            let owner (x : String) := (x.splitOn ".").head!
            let cp := ((cdefs.find? (·.name == c)).map (·.pos)).getD { line := 0, col := 0 }
            throw s!"{cp.show}: {c} has overloads of {mn} a call cannot tell apart, ({sh sb}) in {owner b} and ({sh sa}) in {owner a}: overloads must take disjoint types (an override has the same parameters as its method)"
  -- an override has the signature of the method it overrides, and an
  -- overriding field the inherited field's type (Book of Verse ch. 10)
  -- an override may return a class below the declared one (covariant results)
  let retBelow (a b : Ty) : Bool := a == b || match a, b with
    | .struct S as, .struct T bs => env.classes.contains S && env.classes.contains T && env.isSub S T &&
        env.upArgs S as T == bs
    | _, _ => false
  -- the two methods' types as an instance of class `c` sees them: each
  -- class's type parameters at its type arguments there (#39)
  let inC (c e : String) (t : Ty) : Ty :=
    let cps := ((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k
    t.subst ((((env.sparams.lookup e).getD []).map (·.1)).zip (env.upArgs c cps e))
  let clsOf (n : String) : String := (n.splitOn ".").head!
  let sameSigIn (c : String) (a b : Sig) : Bool :=
    let ea := clsOf a.name
    let eb := clsOf b.name
    -- the methods' own type parameters, after their classes', renamed to the
    -- declaration's (and declared comparable alike)
    let own (sg : Sig) (cls : String) := sg.tparams.drop ((env.sparams.lookup cls).getD []).length
    let (oa, ob) := (own a ea, own b eb)
    -- (renamed apart first, so that a class's type arguments, mapped into
    -- `c`'s, cannot capture them)
    let apart (os : List (String × Bool)) : List (String × Ty) :=
      (os.zip (List.range os.length)).map fun ((x, k), i) => (x, Ty.param s!"$o{i}" k)
    let inA (t : Ty) : Ty := inC c ea (t.subst (apart oa))
    let inB (t : Ty) : Ty := inC c eb (t.subst (apart ob))
    oa.length == ob.length && (oa.map (·.2)) == (ob.map (·.2)) &&
    ((a.params.drop 1).map inA) == ((b.params.drop 1).map inB) &&
      retBelow (inA a.ret) (inB b.ret) && a.decides == b.decides &&
      a.named.map (·.1) == b.named.map (·.1)
  -- an implementation has no heap effect its declaration does not allow
  let fxOver (a b : Sig) : Option String := a.fx.find? (!b.fx.contains ·)
  for (mp, mine, theirs) in overridePairs do
    match allSigs.find? (·.name == mine), allSigs.find? (·.name == theirs) with
    | some a, some b =>
      if !sameSigIn (clsOf mine) a b then throw s!"{mp.show}: {mine} must have the signature of {theirs}, which it overrides"
      if a.suspends != b.suspends then
        throw s!"{mp.show}: {mine} must {if b.suspends then "be" else "not be"} <suspends>, as {theirs}, which it overrides, is{if b.suspends then "" else " not"} (#156)"
      if let some k := fxOver a b then
        throw s!"{mp.show}: {mine} allows the effect <{k}>, which {theirs}, which it overrides, does not"
    | _, _ => pure ()
  -- the implementation a concrete class uses has the signature of every
  -- declaration of the method above it
  for (cp, c, impl, decl) in implChecks do
    -- code generic over the declaring class or interface calls `c`'s
    -- implementation only at its own type arguments (#39, #53)
    -- (judged at the class that holds the implementation, whose Verse Core
    -- type arguments must be the declaring one's, and with the same
    -- signature at those type arguments)
    let q := clsOf decl
    let e := clsOf impl
    let atCore (cls : String) (sg : Sig) : List VTy × VTy :=
      let cenv := { env with tvars := env.coreVars cls }
      ((sg.params.drop 1).map (·.toVTy cenv), sg.ret.toVTy cenv)
    -- (at the type arguments `e` fixes, #142, the declaration's types are
    -- taken at the fixed ones)
    let pinσ : Nat → VTy := fun j => match (env.lowerPins (env.pinsOf e))[j]? with
      | some (some t) => t
      | _ => .var j
    -- (#351) at a class an interface sees through a view, the declaration's
    -- types are taken at the view: its type arguments over the class's
    let viewσ : Nat → VTy := if !env.viewed.contains q then pinσ else
      let X := (List.range (env.coreVars e).length).map fun j => Ty.param (pinArg j) false
      let vw := (env.viewOf q e X).map (Ty.toVTy { env with tvars := X.zipIdx.map fun (x, j) => (pinArg j, x) })
      -- (and at the type arguments `e` fixes, as `pinσ`)
      fun j => (vw.getD j (.var j)).subst pinσ
    let sigOk : Bool := match allSigs.find? (·.name == impl), allSigs.find? (·.name == decl) with
      | some a, some b =>
        let ca := atCore e a
        let cb := atCore q b
        ca.1 == cb.1.map (VTy.subst viewσ) && VTy.sub ca.2 (cb.2.subst viewσ)
      | _, _ => true
    match allSigs.find? (·.name == impl), allSigs.find? (·.name == decl) with
    | some a, some b =>
      if !sameSigIn c a b then
        throw s!"{cp.show}: in {c}, {impl} does not have the signature of {decl}"
      if let some k := fxOver a b then
        throw s!"{cp.show}: in {c}, {impl} allows the effect <{k}>, which {decl} does not"
    | _, _ => pure ()
    if !env.viewed.contains q && !env.sameCorePinned e q then
      throw s!"{cp.show}: {c} uses {impl} for {decl}, but {e} has type parameters that {q} does not have, so code generic over {q} could not give them (#39)"
    if !sigOk then
      throw s!"{cp.show}: {c} uses {impl} for {decl}, but their types differ at {q}'s type arguments (as code generic over {q} sees them), so it could not call it (#53)"
  for (fp, cname, f, sty) in fieldOverrides do
    let cenv := { env with tvars := ((env.sparams.lookup cname).getD []).map fun (v, c) => (v, Ty.param v c) }
    let (t, _) ← (resolveTy cenv fp sty).run {}
    match fieldIndex (env.fields cname) f with
    | some (_, t0) =>
      if !(t == t0) then
        throw s!"{fp.show}: field '{f}' of {cname} must have the type it inherits, {t0.show}, not {t.show}"
    | none => pure ()
  if let some msg := defaultClashes[0]? then throw msg
  let mut fieldDefaultNeeds : List Choice.FirstLift := []
  let mut fieldMethodNeeds : List FnValues.MethodRequest := []
  -- check every field default once, with its struct's type parameters opaque
  -- (a default is elaborated again, at its field's type, at each construction
  -- that omits the field)
  for t in allTops do
    match t with
    | .const _ n none (.structDef _ _ _) =>
      let nps := ((env.sparams.lookup n).getD []).map fun (v, c) => Ty.param v c
      let senv := { env with tvars := (env.sparams.lookup n).getD [] |>.map fun (v, c) => (v, Ty.param v c) }
      let ctx : Ctx := { sigs := allSigs, sigProg, types := senv, canFail := true, inDefaultCheck := true }
      for (f, ft, d) in (env.structs.lookup n).getD [] do
        if let some d := d then
          -- (an inherited default sees its home class's type parameters, #39)
          let home := (env.defaultHome.lookup (n, f)).getD n
          let hσ := (((env.sparams.lookup home).getD []).map (·.1)).zip (env.argsAt n nps home)
          let ctx := { ctx with defaults := [(n, f)], types := { senv with tvars := hσ } }
          match (do coerce d.pos (← elabE ctx d (some ft)) ft : EM Expr).run { env } with
          | .ok (_, st) =>
            fieldMethodNeeds := FnValues.mergeMethodRequests fieldMethodNeeds st.methodNeeds
            fieldDefaultNeeds := fieldDefaultNeeds ++ st.loopFirst.filterMap fun u => match u.lift with
              | .ok l => if l.key.startsWith "defaults:" then some l else none
              | _ => none
          | .error msg => throw s!"{msg} (in the default of field '{f}' of {n})"
    | _ => pure ()
  -- a function: its body under the type environment `env` (which binds the
  -- type parameters `tps` of a generic function to themselves), after the
  -- initialisation of every non-parameter slot (OpenVerse.Core.Typing); its
  -- frame starts with its parameters, then one hidden parameter per type
  -- parameter, holding a value of that type
  -- what each heap effect is, for messages
  let fxWhat : String → String
    | "reads" => "reads a var field"
    | "writes" => "sets a var field"
    | "allocates" => "constructs an object that has a var field or is <unique>"
    | k => k
  let fxCheck (name : String) (allowed : List String) (st : ESt) : Except String Unit := do
    -- writes first, then reads, then allocations
    let order := ["writes", "reads", "allocates"]
    for k in order do
      for (k', kp, via) in st.fx do
        if k' == k && !allowed.contains k then
          let what := match via with
            | some f => s!"{f}, which has the effect <{k}>"
            | none => fxWhat k
          let spec := if allowed.isEmpty then "<computes>" else String.intercalate "" (allowed.map (s!"<{·}>"))
          let fix := if allowed.isEmpty then "remove <computes>" else s!"add <{k}> or <transacts>"
          throw s!"{kp.show}: {name} {what}, which its effects ({spec}) do not allow: {fix}"
  let elabFn (env : TyEnv) (p : Pos) (name : String) (ps : List SParam) (ptys : List Ty) (ret : Ty)
      (decides : Bool) (allowed : List String) (tps : List (String × Bool)) (body : SExpr)
      (suspends : Bool := false) (selfTps : List String := [])
      (selfFieldOf : Option (String → Option Nat) := none) (scopeClass : Option String := none) :
      Except String (Fn × List VTy × List (String × Ty) × Option Pos × List Refine.Lift × List LoopUse × FrameRefs.Info × List String × List FnValues.MethodRequest) := do
    -- (#209) the values of `selfTps` come from the receiver's hidden
    -- fields, in slots after the hidden parameters: a method's own class's
    -- (`C.M`), or as `selfFieldOf` says (a cast's branch, #250, the cast
    -- target's, of the object, its first parameter too)
    let dictTps := tps.filter (fun (v, _) => !selfTps.contains v) ++ tps.filter (fun (v, _) => selfTps.contains v)
    let selfCls := (name.splitOn ".").headD ""
    let selfField (v : String) : Nat :=
      ((selfFieldOf.getD fun v => env.witnessField? selfCls v) v).getD 0
    -- (a cast's branch, #250: each opened type parameter's value must have
    -- a hidden field to come from, never another field)
    if let some sf := selfFieldOf then
      if let some v := selfTps.find? fun v => (sf v).isNone then
        throw s!"{p.show}: internal error: no hidden field holds a value of the type parameter {v} the cast opens (#250)"
    let env := if selfTps.isEmpty then env else
      { env with dictOrder := dictTps.map (·.1),
                 selfWitness := selfTps.map fun v => (v, selfField v) }
    let locals := ((ps.zip (List.range ps.length)).zip ptys).map fun ((prm, i), t) =>
      ({ name := prm.name, slot := i, ty := t, mutable := false } : Local)
    for (prm, i) in ps.zip (List.range ps.length) do
      if ps.take i |>.any (·.name == prm.name) then throw s!"{p.show}: duplicate parameter '{prm.name}'"
    let base : Ctx := {
      sigs := allSigs
      sigProg := sigProg
      locals := locals.reverse
      types := env
      fnFx := allowed
      canFail := decides
      retTy := ret
      dictBase := ps.length
      suspends := suspends
      dictVars := dictTps.map (·.1) }
    let ctx ← functionBodyCtx opts base p name tps scopeClass
    let locals := ctx.locals.reverse
    let hidden := dictTps.map fun (v, c) => Ty.param v c
    let arity := ps.length + hidden.length - selfTps.length
    let st0 : ESt := {
      env, nslots := ps.length + hidden.length, slotTys := (ptys ++ hidden).toArray,
      frameSlots := locals.filterMap fun l => l.storage.map (l.slot, ·) }
    -- (#283) its calls of overloaded functions with several values chosen
    let ((r, _), st) ← elabBodyOv ctx body (some ret) st0
    let (e, st) ← (coerce p r ret).run st
    let e := if ret == .void then Expr.seq e (.lit .void) else e
    let selfInits : List Expr := (dictTps.drop (hidden.length - selfTps.length)).map fun (v, _) =>
      .heap (.get (selfField v)) [.local 0]
    let inits ← match (st.slotTys.toList.drop (ps.length + hidden.length)).mapM
        (slotDefault env ps.length (ptys ++ hidden.take (hidden.length - selfTps.length)) []) with
      | .ok ds => pure (selfInits ++ ds)
      | .error msg => throw s!"{p.show}: in {name}: {msg}"
    fxCheck name allowed st
    return ({ name, arity, nslots := st.nslots, decides, writes := allowed.contains "writes",
              body := initPrefixE arity inits e },
      spawnParamTypes env name (st.slotTys.toList.map (Ty.toVTy env)), st.fnNeeds, st.errAt, st.castNeeds, st.loopFirst,
      { explicit := ps.length, copies := st.frameCopies, slots := st.frameSlots.map fun (i, s) =>
          (i, { frame := s.frame, name := s.name, args := s.args.map (Ty.toVTy env) }) }, st.eagerNeeds, st.methodNeeds)
  -- (the accessors come right after the functions, #157)
  env := { env with fieldAccBase := tops.length + gsigs.size }
  let genvOf (g : Sig) : TyEnv := { env with tvars := g.tparams.map fun (v, c) => (v, Ty.param v c) }
  let mut fns : Array Fn := #[]
  let mut slotTys : Array (List VTy) := #[]
  let mut frameInfo : Array FrameRefs.Info := #[]
  let mut fnNeeds : List (String × Ty) := []
  let mut methodNeeds : List FnValues.MethodRequest := fieldMethodNeeds
  -- (where each function calls `Err()`, by its index, #235)
  let mut errs : Array (Option Pos) := #[]
  let mut castNeeds : List Refine.Lift := []
  -- (the lazily taken functions with several values that contexts taking
  -- their first success consume, #246)
  let mut loopFirst : List LoopUse := fieldDefaultNeeds.map fun l =>
    { g := "", pos := l.pos, itemCode := .lit .void, argSet := none, lift := .ok l }
  let mut eagerNeeds : List String := []
  for (top, idx) in tops.zip (List.range tops.length) do
    let sig := sigs[idx]!
    match top with
    | .fn p n ps _ _ _ body =>
      let (fn, tys, needs, err, casts, lf, frames, eager, methodUses) ← elabFn env p n ps sig.params sig.ret sig.decides sig.fx [] body sig.suspends
      eagerNeeds := eagerNeeds ++ eager
      fnNeeds := fnNeeds ++ needs
      methodNeeds := FnValues.mergeMethodRequests methodNeeds methodUses
      castNeeds := castNeeds ++ casts
      loopFirst := loopFirst ++ lf
      fns := fns.push fn
      errs := errs.push err
      slotTys := slotTys.push tys
      frameInfo := frameInfo.push frames
    | .const p n _ body =>
      -- a constant is computed at each use, so it would be a new object each
      -- time (until Verse Core has global state)
      if sig.ret.holdsMutable env then
        throw s!"{p.show}: the constant {n} would hold an object with var fields or of a <unique> class, which would be a new one at each use: make it a function"
      let ctx : Ctx := { sigs := allSigs, sigProg, types := env }
      let (r, st) ← elabBodyOv ctx body (some sig.ret) { env }
      let (e, st) ← (coerce p r.1 sig.ret).run st
      fnNeeds := fnNeeds ++ st.fnNeeds
      methodNeeds := FnValues.mergeMethodRequests methodNeeds st.methodNeeds
      castNeeds := castNeeds ++ st.castNeeds
      loopFirst := loopFirst ++ st.loopFirst
      eagerNeeds := eagerNeeds ++ st.eagerNeeds
      let tys := st.slotTys.toList.map (Ty.toVTy env)
      frameInfo := frameInfo.push {}
      -- slots start like a function's (a class-typed one as a placeholder)
      let inits ← match st.slotTys.toList.mapM (slotDefault env 0 [] []) with
        | .ok ds => pure ds
        | .error msg => throw s!"{p.show}: in {n}: {msg}"
      fxCheck n sig.fx st
      fns := fns.push { name := n, arity := 0, nslots := st.nslots, decides := false,
                        writes := sig.fx.contains "writes", body := initPrefixE 0 inits e }
      errs := errs.push st.errAt
      slotTys := slotTys.push tys
    | .classDef .. => pure ()   -- expanded above
  -- each generic function is elaborated once, with its type parameters
  -- opaque, as Verse checks it, into one Verse Core function whose types
  -- mention type variables; `Prog.checkTypes` checks it once, for every
  -- instantiation (`Typed.subst`)
  for (top, g) in generics.zip gsigs.toList do
    match top with
    | .fn p n ps _ effs _ body =>
      -- (a class's copy of an interface's default, #53, elaborated in the
      -- interface's scope)
      let scope := copyScope? effs
      let (fn, tys, needs, err, casts, lf, frames, eager, methodUses) ← elabFn (genvOf g) p n ps g.params g.ret g.decides g.fx g.tparams body g.suspends
        g.selfTps ((opts.castRequests.find? (·.name == n)).map fun l => fun v =>
          (l.opened.lookup v).bind (env.witnessField? l.target ·)) scope
      fnNeeds := fnNeeds ++ needs
      methodNeeds := FnValues.mergeMethodRequests methodNeeds methodUses
      eagerNeeds := eagerNeeds ++ eager
      castNeeds := castNeeds ++ casts
      loopFirst := loopFirst ++ lf
      fns := fns.push fn
      errs := errs.push err
      slotTys := slotTys.push tys
      frameInfo := frameInfo.push frames
    | _ => pure ()
  -- (#214) functions wanted as values at types no class of theirs gives:
  -- the program is elaborated again, with classes for them, so this one,
  -- with placeholders, goes no further
  -- (#243) and branches of casts that refine type arguments, lifted into
  -- functions
  if !eagerNeeds.isEmpty then
    return { prog := default, sigs := { fns := [] }, slotTys := [], eagerNeeds := eagerNeeds.eraseDups }
  let defaults := loopFirst.filterMap fun u => match u.lift with
    | .ok l => if l.key.startsWith "defaults:" then some l else none
    | _ => none
  if !fnNeeds.isEmpty || !methodNeeds.isEmpty || !castNeeds.isEmpty || !defaults.isEmpty then
    let casts := castNeeds.foldl (fun acc l => if acc.any (·.key == l.key) then acc else acc ++ [l]) []
    return { prog := default, sigs := { fns := [] }, slotTys := [], fnNeeds := fnNeeds.eraseDups, methodNeeds, castNeeds := casts, loopNeeds := defaults.foldl (fun acc l => if acc.any (·.key == l.key) then acc else acc ++ [l]) [] }
  let mainSig ← match sigs.toList.find? (·.name == (if opts.entry.isSome then "$Do" else "Main")) with
    | some s =>
      if s.isConst || !s.params.isEmpty then throw "Main must be a function with no parameters"
      pure s
    | none => throw "the program has no Main() function"
  -- with prototypes, the program starts with a prelude that allocates them
  -- and then calls `Main` (#37)
  let mut protoList := env.protos.map fun (_, t, vs) => (t, vs)
  let fsigs0 := sigs.toList.map (fun s => (spawnParamTypes env s.name (s.params.map (Ty.toVTy env)), s.ret.toVTy env)) ++
    gsigs.toList.map fun g =>
      let genv := genvOf g
      let dictTys : List Ty := (g.tparams.filter fun (vc : String × Bool) => !g.selfTps.contains vc.1).map
        fun (vc : String × Bool) => Ty.param vc.1 vc.2
      (spawnParamTypes genv g.name ((g.params ++ dictTys).map (Ty.toVTy genv)), g.ret.toVTy genv)
  -- the class table: the fields of each class, by tag (#34); the prototypes (#37)
  -- (a parametric class's field types mention its type parameters, #39)
  -- each field as `TyEnv.fieldSrc` gives it (the topmost interface that
  -- declares it, else the topmost class in the chain that has it), in
  -- terms of the Verse Core type arguments the hierarchy shares: an
  -- `intbox := class(base(int))`'s inherited `Value` is `var 0`, as in `base`
  let mut classTable := env.classes.map fun d =>
    if env.isRefClass d then (env.fields d).map fun (f, t, _) =>
      (env.coreFieldTy d f).getD (t.toVTy { env with tvars := env.coreVars d })
    else []
  let protos := env.protos.map fun (d, t, _) => (t, (env.coreArgs d []).map (Ty.toVTy env))
  -- (a class below an interface referred to through views has pins on all of
  -- its Verse Core type arguments, so that a dispatch through a view opens
  -- them, `Typed.dispatch_view`, #351)
  let pins := env.classes.map fun d =>
    if env.isRefClass d then env.lowerPins (env.dispatchPins d) else []
  -- concurrency (#156): each <suspends> function `g` becomes a frame class
  -- and the functions `g$new`, `g$reset` and `g$resume` (`Suspend.lean`);
  -- `g`'s own index is `g$resume`'s, as only suspends code calls it
  -- the accessors (#157): for each (class, field), `get(Self)` and
  -- `set(Self, V)`, generic over the class's type argument positions
  let mut accSigs : Array (List VTy × VTy) := #[]
  for (d, f) in env.fieldAcc do
    let tag := env.tagOf d
    let kd := ((fieldIndex (env.fields d) f).map (·.1)).getD 0
    let m := (env.coreArgs d (((env.sparams.lookup d).getD []).map fun (v, c) => Ty.param v c)).length
    let selfTy : VTy := .ref [tag] ((List.range m).map VTy.var)
    let fTy : VTy := ((classTable[tag]?).bind (·[kd]?)).getD .int
    fns := fns.push { name := s!"{d}.$get.{f}", arity := 1, nslots := 1, decides := false, writes := false,
                      body := .heap (.get kd) [.local 0] }
    slotTys := slotTys.push [selfTy]
    accSigs := accSigs.push ([selfTy], fTy)
    fns := fns.push { name := s!"{d}.$set.{f}", arity := 2, nslots := 2, decides := false, writes := true,
                      body := .heap (.set kd) [.local 0, .local 1] }
    slotTys := slotTys.push [selfTy, fTy]
    accSigs := accSigs.push ([selfTy, fTy], fTy)
  let fsigs0 := fsigs0 ++ accSigs.toList
  let mut fsigs := fsigs0
  let mut frameClasses : Array (List VTy) := #[]
  let mut framePins : List (List (Option VTy)) := []
  let mut mainCall : Expr := .call mainSig.idx []
  -- (an error of the lowering names a function: with its position)
  let inFn := inFnMsg (tops ++ generics)
  -- (a refined test, #142, of classes whose pins the receiver's closed type
  -- arguments rule out can never pass, and the checker types such a test
  -- only when the pins can agree: it goes, #186)
  let S00 : Sigs := { fns := fsigs0, classes := classTable, protos, pins }
  for gi in List.range fns.size do
    let fn := fns[gi]!
    fns := fns.set! gi { fn with body := Suspend.pruneDead S00 ((slotTys[gi]?).getD []) fn.body }
  -- (#235) the functions with several values computed at their calls
  checkEager fns errs fun g => ((tops ++ generics).findSome? fun
    | .fn p n .. => if n == g then some p else none
    | _ => none)
  -- (#246) and functions of their own for the lazily taken calls whose
  -- effects need them: the program is elaborated again, with them
  let loopNeeds ← checkLoopFirst fns loopFirst opts.loopRequests
  if !loopNeeds.isEmpty then
    return { prog := default, sigs := { fns := [] }, slotTys := [], loopNeeds }
  let (capturedFns, capturedSlots, capturedSigs) ← FailCapture.lower fns slotTys S00
  fns := capturedFns
  slotTys := capturedSlots
  let fsigs0 := capturedSigs.fns
  fsigs := fsigs0
  let beforeConcurrency := fns
  if usesConc then
    let (fns1, slotTys1, fsigs1, classTable1, frameClasses1, mainCall1, framePins1, schedMore) ←
      lowerOpening fun forced =>
        lowerConcurrency env sigs gsigs mainSig fsigs0 protos pins inFn fns slotTys fsigs classTable forced frameInfo
    if !schedMore.isEmpty then
      let schedTag := env.tagOf "$sched"
      protoList := protoList.map fun (t, vs) => if t == schedTag then (t, vs ++ schedMore) else (t, vs)
    fns := fns1
    slotTys := slotTys1
    fsigs := fsigs1
    classTable := classTable1
    frameClasses := frameClasses1
    mainCall := mainCall1
    framePins := framePins1
  let mut main := mainSig.idx
  if !protoList.isEmpty || mainSig.suspends then
    main := fns.size
    fns := fns.push { name := "$Main", arity := 0, nslots := 0, decides := mainSig.decides,
                      writes := mainSig.fx.contains "writes" || mainSig.suspends,
                      body := protoPrelude protoList mainCall }
    slotTys := slotTys.push []
    fsigs := fsigs ++ [([], if mainSig.suspends then VTy.void else mainSig.ret.toVTy env)]
  if usesConc then
    fns := CompilerWrites.propagate beforeConcurrency fns
  let P : Prog := { fns := fns.toList, main }
  if !P.check then
    let bad := P.fns.filter fun fn => (!fn.decides && fn.body.mayFail P) ||
      (!fn.writes && fn.body.writesHeap P) || !(fn.body.scoped P fn.nslots)
    throw s!"internal error: the elaborated program does not pass Prog.check ({bad.map (·.name)})"
  if !P.checkControl then throw "internal error: the elaborated program does not pass Prog.checkControl"
  -- (the frame classes' pins after the classes', #244)
  let pins := (List.range classTable.length).map (fun t => (pins[t]?).getD []) ++ framePins
  let S : Sigs := { fns := fsigs, classes := classTable ++ frameClasses.toList, protos, pins }
  if !P.checkTypes S slotTys.toList then
    -- name what fails, for a bug report
    let bad := (List.range P.fns.length).find? fun f =>
      match P.fns[f]?, S.fns[f]?, slotTys[f]? with
      | some fn, some (ps, τ), some Γ => !checkFn S fn ps τ Γ
      | _, _, _ => true
    let which := match bad with
      | some f =>
        -- (the innermost statement of its body the checker rejects, in sequence)
        let rec firstBad (fuel : Nat) (Γ : List VTy) (ρ : VTy) (e : Expr) : Expr :=
          match fuel, e with
          | f + 1, .seq a b =>
            if (tc S Γ ρ a none).isNone && (tc S Γ ρ a (some VTy.void)).isNone then firstBad f Γ ρ a
            else firstBad f Γ ρ b
          | _, e => e
        -- (first the slots' initial values, which `checkDefault` checks
        -- apart from the statements, then the body after them)
        let rec badInit (a k : Nat) (Γ : List VTy) : List VTy → Expr → Sum String Expr
          | [], e => .inr e
          | t :: ts, e => match e with
            | .seq (.assign i d) rest =>
              if i == k && checkDefault S a Γ d t then badInit a (k + 1) Γ ts rest
              else .inl s!"\n-- initial value of slot {k} rejected (type {repr t}): {d.compact}"
            | _ => .inl s!"\n-- no initial value for slot {k}"
        let badStmt : String := match P.fns[f]?, S.fns[f]?, slotTys[f]? with
          | some fn, some (_, τ), some Γ => match badInit fn.arity fn.arity Γ (Γ.drop fn.arity) fn.body with
            | .inl msg => msg
            | .inr b => s!"\n-- first rejected:\n{(firstBad 10000 Γ τ b).compact "   "}"
          | _, _, _ => ""
        let dump := if !opts.debug then "" else
          badStmt ++ s!"\n-- body:\n{((P.fns[f]?).map (fun (fn : Fn) => fn.body.compact "   ")).getD "?"}\n-- arity: {(P.fns[f]?).map Fn.arity}" ++
          s!"\n-- slot types: {repr (slotTys[f]?)}\n-- signature: {repr (S.fns[f]?)}"
        s!" (in {((P.fns[f]?).map Fn.name).getD "?"}){dump}"
      | none => if !checkPrelude P S then " (the prototypes)" else ""
    throw s!"internal error: the elaborated program does not pass Prog.checkTypes{which}"
  return { prog := P, sigs := S, slotTys := slotTys.toList, fnNeeds := fnNeeds.eraseDups, methodNeeds }

/-- `F$ovN` (an overload, #74) shown as `F`: every `$ov` and the digits after it removed. -/
def stripOv (msg0 : String) : String := Id.run do
  -- `K$default$F` (a default an overloaded constructor fills in) is "the default of F"
  let msg := match msg0.splitOn "$default$" with
    | [] | [_] => msg0
    | first :: rest =>
      let dropName (x : String) : String :=
        String.ofList (x.toList.reverse.dropWhile (fun (c : Char) => c.isAlphanum || c == '_')).reverse
      rest.foldl (fun acc part => dropName acc ++ "the default of " ++ part) first
  -- (an array: a list's indexing and length are linear, which made this
  -- quadratic in the message, minutes for `OPENVERSE_DEBUG`'s dump)
  let cs := msg.toList.toArray
  let mut out : String := ""
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '$' && i + 2 < cs.size && cs[i+1]! == 'o' && cs[i+2]! == 'v' then
      i := i + 3
      while i < cs.size && cs[i]!.isDigit do i := i + 1
    else
      out := out.push cs[i]!
      i := i + 1
  return out

/-- Nested consumers can discover a continuation and its refining branches
    in separate rounds. Bound discovery by source nesting, rather than a
    fixed four rounds; every round must still add a new request. -/
partial def liftDepth (e : SExpr) : Nat :=
  1 + e.children.foldl (fun n child => max n (liftDepth child)) 0

partial def topLiftDepth : STop → Nat
  | .fn _ _ ps _ _ _ body =>
    (ps.filterMap (·.default)).foldl (fun n e => max n (liftDepth e)) (liftDepth body)
  | .const _ _ _ e => liftDepth e
  | .classDef _ _ _ _ _ _ fields _ methods =>
    methods.foldl (fun n t => max n (topLiftDepth t))
      (fields.foldl (fun n (_, _, e, _) => max n (e.map liftDepth |>.getD 0)) 0)

/-- Named defaults can discover forwarding helpers along a dependency
    chain. Interface copies may instantiate each source method per class. -/
partial def topDefaultCount : STop → Nat
  | .fn _ _ ps _ _ _ _ => (ps.filter (·.named)).length
  | .classDef _ _ _ _ _ _ _ _ ms => ms.foldl (fun n m => n + topDefaultCount m) 0
  | _ => 0

/-- Elaborate a parsed program (`elabProgramCore`), with the names of the
    functions a constructor or an overload becomes shown as written: `K$init`
    is `K<constructor>`, `F$ov1` is `F` (names with `$` are never the user's). -/
def elabProgram (allTops00 : List STop) (opts : Options := {}) : Except String Compiled :=
  let defaults := allTops00.foldl (fun n t => n + topDefaultCount t) 0
  let classes := allTops00.filter (fun | .classDef .. => true | _ => false) |>.length
  let rounds := max 4 (4 * (allTops00.foldl (fun n t => max n (topLiftDepth t)) 0 + defaults * (classes + 1)))
  -- (#214) again with the functions wanted as values at closed function
  -- types: each round asks for new ones only, so a few rounds do
  let rec go (fuel : Nat) (opts : Options) : Except String Compiled := do
    let c ← elabProgramCore allTops00 opts
    if !c.eagerNeeds.isEmpty then return c
    -- (#243) and with the branches of casts that refine type arguments
    let casts := c.castNeeds.filter fun l => !opts.castRequests.any (·.key == l.key)
    -- (#246) and with functions of their own for lazily taken calls
    let loops := c.loopNeeds.filter fun l => !opts.loopRequests.any (·.key == l.key)
    -- A newly materialized dispatch-default helper can reveal heap effects
    -- absent from an earlier suffix trial. Rediscover consumers after those
    -- helpers have participated in effect inference; their cached stage
    -- interfaces, prefixes and resume methods must agree on permissions.
    -- Each restart retains the new bridges, so discovery still progresses.
    let methods := c.methodNeeds.filter fun r => !opts.methodRequests.any (·.key == r.key)
    let newDefaults := loops.filter fun l => defaultBridge l.name
    if !newDefaults.isEmpty then
      match fuel with
      | fuel + 1 =>
        let bridges := opts.loopRequests.filter fun l => defaultBridge l.name || spawnAdapter l.name
        return ← go fuel { opts with
          fnRequests := (opts.fnRequests ++ c.fnNeeds).eraseDups,
          methodRequests := FnValues.mergeMethodRequests opts.methodRequests methods,
          castRequests := [], loopRequests := bridges ++ newDefaults }
      | 0 => throw "internal error: default forwarding helpers still to infer after several elaborations"
    if !methods.isEmpty then
      match fuel with
      | fuel + 1 => return ← go fuel { opts with
          methodRequests := FnValues.mergeMethodRequests opts.methodRequests methods,
          fnRequests := (opts.fnRequests ++ c.fnNeeds).eraseDups,
          castRequests := opts.castRequests ++ casts, loopRequests := opts.loopRequests ++ loops }
      | 0 => throw "internal error: method variance adapters still to infer after several elaborations"
    match fuel, c.fnNeeds.filter (!opts.fnRequests.contains ·) with
    | fuel + 1, new@(_ :: _) =>
      go fuel { opts with fnRequests := opts.fnRequests ++ new, castRequests := opts.castRequests ++ casts,
                          loopRequests := opts.loopRequests ++ loops }
    | fuel + 1, [] =>
      if casts.isEmpty && loops.isEmpty then
        if c.castNeeds.isEmpty && c.loopNeeds.isEmpty then return c
        throw "internal error: a cast that refines type arguments, or a lazily taken call's function, was asked for again (#243, #246)"
      go fuel { opts with castRequests := opts.castRequests ++ casts, loopRequests := opts.loopRequests ++ loops }
    | 0, [] =>
      if c.castNeeds.isEmpty && c.loopNeeds.isEmpty then return c
      throw "internal error: casts that refine type arguments, or lazily taken calls, still to lift after several elaborations (#243, #246)"
    -- (a program with a placeholder left is never given out)
    | 0, _ :: _ => throw "internal error: functions still wanted as values after several elaborations (#214)"
  -- (#351) and with hidden fields for all of the type parameters of the
  -- classes that ask for them, each round more
  let rec withWitness (fuel : Nat) (opts : Options) : Except String Compiled := do
    let c ← go rounds opts
    if c.witnessNeeds.isEmpty then return c
    match fuel with
    | fuel + 1 => withWitness fuel { opts with witnessAll := opts.witnessAll ++ c.witnessNeeds }
    | 0 => throw "internal error: classes still asking for hidden fields after several elaborations (#351)"
  -- A restart discards helpers prepared for the lazy group; their bodies
  -- must be discovered again after its calls become eager. Each restart
  -- forces a new source function's group, so source definitions bound it.
  let count := allTops00.foldl (fun n t => n + match t with
    | .fn .. => 1
    | .classDef _ _ _ _ _ _ _ _ ms => ms.length
    | _ => 0) 1
  let rec withEager (fuel : Nat) (opts : Options) : Except String Compiled := do
    let c ← withWitness (max 8 (classes + 1)) opts
    if c.eagerNeeds.isEmpty then return c
    let new := c.eagerNeeds.filter (!opts.eagerRequests.contains ·)
    match fuel, new with
    | fuel + 1, _ :: _ =>
      withEager fuel { opts with eagerRequests := opts.eagerRequests ++ new, loopRequests := [], castRequests := [] }
    | _, _ => throw "internal error: mutual generator instances still changing after eager lowering (#283)"
  (withEager count opts).mapError fun msg =>
    FnValues.pretty (((stripOv (msg.replace "$init" "<constructor>")).replace "::" ".").replace "$replaceAll" "ReplaceAll")

/-- Parse and elaborate Verse source text. -/
def compileChecked (src : String) (opts : Options := {}) : Except String Compiled := do
  elabProgram (← parseProgram src) opts

/-- Parse and elaborate Verse source text. -/
def compile (src : String) (opts : Options := {}) : Except String Prog := do
  return (← compileChecked src opts).prog

/-- Compile loaded definitions (`Front.loadProgram`) with shell arguments,
    bound to `Args` when given or mentioned, and an optional `do` expression. -/
def compileTops (tops : List STop) (args : List String) (mentionsArgs : Bool) (doExpr : Option String)
    (debug : Bool := false) (profile : SourceProfile := .full) : Except String Prog := do
  let entry ← match doExpr with
    | some t => some <$> parseExprText t
    | none => pure none
  let useArgs := !args.isEmpty || mentionsArgs
  return (← elabProgram tops { args := if useArgs then some args else none, entry, debug, profile }).prog

/-- Compile with shell arguments (bound to `Args` when given or used) and an
    optional `do` expression, as `openverse run FILE ARG… do EXPR` does. -/
def compileWith (src : String) (args : List String) (doExpr : Option String)
    (profile : SourceProfile := .full) : Except String Prog := do
  let entry ← match doExpr with
    | some t => some <$> parseExprText t
    | none => pure none
  let useArgs := !args.isEmpty || (src.splitOn "Args").length > 1
  compile src { args := if useArgs then some args else none, entry, profile }

end OpenVerse.Front
