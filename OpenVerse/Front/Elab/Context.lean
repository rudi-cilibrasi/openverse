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
import OpenVerse.Front.ConcurrencyPrelude
import OpenVerse.Front.PreludeNeeds
import OpenVerse.Front.Profile
import OpenVerse.Front.EffectPolicy
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
import OpenVerse.Front.ChoiceTypes
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

/-- The implicit receiver, distinguished from an ordinary parameter that a
    source function happens to name Self. Extracted methods use $Self. -/
def Sig.hasReceiver (s : Sig) : Bool :=
  s.pnames.head? == some "$Self" || (s.pnames.head? == some "Self" &&
    match s.params.head? with
    | some (.struct owner _) => s.name.startsWith (owner ++ ".")
    | _ => false)

/-- Default-dispatch helpers are private forwarding functions, with defaults
    evaluated in the selected implementation's own type context. -/
def defaultBridge (n : String) : Bool := (n.splitOn "$dispatchDefaults").length > 1

/-- Dictionary forwarders evaluating omitted defaults retain caller task ownership. -/
def choiceDefaultBridge (n : String) : Bool :=
  n.startsWith "$choiceOperationDictionary" && (n.splitOn "$choiceDefault").length > 1

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
  choiceCoercions : List (Local × Ty × Ty) := []
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
      (#208), inside a `loop`, that have no `break` that leaves them: the
      loop they are compiled to does not forward one (`elabFirstGo`). -/
  inChoice : Bool := false
  /-- In the clauses of a failure context that takes a choice's values
      (#208): a choice that reaches the elaborator here is in a place it
      cannot be lifted from. -/
  inTaking : Bool := false
  /-- The internal loop that propagates a failed continuation outcome. -/
  forOutcomeSlot : Option Nat := none
  /-- A source-loop break crossing the internal loops of lazy producers and
      of first successes (`firstE`), each of which forwards it. -/
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
  /-- (#283) At each of `TyEnv.familySites` elaborated: the root of its
      method above its receiver's class, for the next round's inlining. -/
  familyNeeds : List (Pos × String) := []
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

/-- Give a disposable polymorphic suffix trial its own type witnesses.
    The generated continuation will obtain them from its actual arguments. -/
def choiceTypeContext (ctx : Ctx) (plan : ChoiceTypes.Plan) : EM Ctx := do
  let types := { ctx.types with
    tvars := plan.params.map (fun (n, c) => (n, Ty.param n c)) ++ ctx.types.tvars }
  let names := ctx.dictVars ++ plan.params.map (·.1)
  let base := (← get).nslots
  for name in names do
    let st ← get
    let ty := (types.tvars.lookup name).getD (.param name false)
    set { st with nslots := st.nslots + 1, slotTys := st.slotTys.push ty }
  return { ctx with dictBase := base, dictVars := names, types }

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
    if n == env.concurrencyName "subscribable_event" && ts == [.void] && env.classes.contains "$subscription" then
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
partial def argNeedsTypeWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (a : SExpr) : EM Bool := do
  if ctx.argNeedsType a then return true
  let compound (es : List SExpr) : EM Bool := do
    if !(← es.anyM (argNeedsTypeWith elabE ctx)) then return false
    -- A grouped positional argument can need a later named argument's
    -- type. Keep compounds that already infer naturally in the first pass.
    let saved ← get
    match (elabE { ctx with typeOnly := true, callInstanceProbe := none } a none).run saved with
    | .ok (_, probed) =>
      modify fun st => { st with natTys := probed.natTys, methodReceivers := probed.methodReceivers }
      return false
    | .error _ => return true
  match a with
  | .app _ (.ident _ "$callSingleton") [e] false => argNeedsTypeWith elabE ctx e
  | .tuple _ es | .arrayLit _ es => compound es
  | .optionLit _ e => compound [e]
  | .mapLit _ kvs => compound (kvs.flatMap fun (k, v) => [k, v])
  | .block _ es => compound es.getLast?.toList
  | .ite _ _ yes no => compound (yes :: no.toList)
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
      ctx.constructOrigin, ctx.unrefine) ++ (if ctx.choiceCoercions.isEmpty then "" else
        reprStr (ctx.choiceCoercions.map fun (dictionary, source, target) => (dictionary.name, source, target)))
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

/-- Whether this elaboration knows if an expression can fail: not one for
    types, nor one to be done again with functions as values (#214, #231)
    or with the families of methods' uses (#283), which may make a call
    fail or have several values. -/
def Ctx.failabilityKnown (ctx : Ctx) : EM Bool := do
  let st ← get
  return st.fnNeeds.isEmpty && st.methodNeeds.isEmpty && ctx.types.familySites.isEmpty && !ctx.typeOnly

/-- (#283) A use `R.M` at `p` whose family of methods only the class of
    `R` tells, one of `TyEnv.familySites`: the root of `M` above that class
    noted, none (`""`) for a receiver of another type. -/
def Ctx.noteFamily (ctx : Ctx) (p : Pos) (recv : Ty) (m : String) : EM Unit := do
  if ctx.types.familySites.contains (p, m) then
    let root := match recv with
      | .struct c _ => ((ctx.rootsOf c m).head?).getD ""
      | _ => ""
    modify fun st => { st with familyNeeds := (p, root) :: st.familyNeeds }

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

/-- (#351) For a reference of type `a` converted to `b`, an interface
    referred to through views: the classes of `a`'s reference that can be a
    `b` (those whose view gives `b`'s type arguments, unless closed ones
    differ), and whether a reference to them is a `b` in Verse Core. -/
def TyEnv.viewFits (env : TyEnv) (a b : Ty) : Option (List Nat × Bool) :=
  match a.toVTy env, b.toVTy env with
  | .ref ts as, .vref es bs =>
    let closedOff (t : Nat) : Bool := match es.find? (·.1 == t) with
      | some (_, φ) =>
        φ.all (·.varsBelow as.length) &&
          ((φ.map (VTy.inst as)).zip bs).any fun (u, w) => !u.mentionsVar && !w.mentionsVar && decide (u ≠ w)
      | none => false
    let fits := ts.filter (!closedOff ·)
    some (fits, (VTy.ref fits as).sub (.vref es bs))
  | _, _ => none

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
  if refUp env a b then
    -- (#351: to an interface referred to through views, from a reference
    -- whose classes include one whose view gives other type arguments,
    -- closed ones that differ, which no object of that type can be: a test
    -- of the others, its object always one of them)
    match a.toVTy env, b.toVTy env, env.viewFits a b with
    | .ref ts as, .vref es bs, some (fits, ok) =>
      if (VTy.ref ts as).sub (.vref es bs) then return some e
      if fits.length == ts.length || !ok then return some e
      let x ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push a })
      let y ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push b })
      return some (.seq (.assign x e) (.ite (.assign y (.heap (.isTag fits) [.local x])) (.local y) (.prim .userErr [])))
    | _, _, _ => return some e
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

/-- Save rational operands in written order, then pass their int parts to
    an exact primitive. Repeated projections never repeat an operand. -/
def rationalBinary (p : Pos) (op : Prim) (a b : R) : EM Expr := do
  let x ← fresh .rational
  let y ← fresh .rational
  let ae ← coerce p a .rational
  let be ← coerce p b .rational
  let parts (slot : Nat) := [Expr.prim (.tupGet 0) [.local slot], .prim (.tupGet 1) [.local slot]]
  return .seq (.assign x ae) (.seq (.assign y be) (.prim op (parts x ++ parts y)))

def roundRational (up : Bool) (e : Expr) : EM Expr := do
  let tr ← fresh .rational
  let tz ← fresh .int
  let op := if up then Prim.ceilDiv else .floorDiv
  let parts := [Expr.prim (.tupGet 0) [.local tr], .prim (.tupGet 1) [.local tr]]
  return .seq (.assign tr e) (Expr.orE tz (.prim op parts) (.lit (.int 0)))

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

/-- A generated result packet joins each field independently. In particular,
    an erased value must not erase the packet's remaining bindings/flags. -/
partial def choiceResultType (env : TyEnv) (types : List Ty) : Option Ty := do
  let first ← types.head?
  if types.all (· == first) then return types.foldl Ty.commonBounds first
  if let some children := types.mapM (fun | .arr t => some t | _ => none) then
    return .arr (← choiceResultType env children)
  if let some children := types.mapM (fun | .opt t => some t | _ => none) then
    return .opt (← choiceResultType env children)
  if let .tup ts := first then
    if let some rows := types.mapM (fun
        | .tup us => if us.length == ts.length then some us else none
        | _ => none) then
      return .tup (← (List.range ts.length).mapM fun j =>
        choiceResultType env (rows.map fun row => row[j]!))
  types.foldlM (fun a b =>
    if a == .void || b == .void then some .void else
    (joinTy env a b none).orElse fun _ =>
      if ambiguousJoin env a b then none else some .any) first

/-- A common class view suffices when the suffix only accesses fields whose
    instantiated types agree in every alternative. Bare values, methods and
    local type definitions keep their original static types instead. -/
partial def choiceFieldsOnly (env : TyEnv) (binding : String) (types : List Ty)
    (view : Ty) (body : SExpr) : Bool :=
  match body with
  | .member _ (.ident _ name) field =>
    if name != binding then true else
      match view with
      | .struct base args =>
        match (env.fields base args).find? (·.1 == field) with
        | none => false
        | some (_, ty, _) => types.all fun
          | .struct n ts => ((env.fields n ts).find? (·.1 == field)).any fun (_, actual, _) =>
              reprStr actual == reprStr ty
          | _ => false
      | _ => false
  | .ident _ name => name != binding
  | .structDef .. | .enumDef .. | .refineDef .. => false
  | e => e.children.all (choiceFieldsOnly env binding types view)

def choiceTypePlan (ctx : Ctx) (stem binding : String) (types : List Ty)
    (suffix : List SExpr) : Option ChoiceTypes.Plan := do
  let plan ← ChoiceTypes.generalize ctx.types stem types
  let first ← types.head?
  if let some view := types.tail.foldlM (fun a b => joinTy ctx.types a b none) first then
    if let .struct n _ := view then
      if ctx.types.classes.contains n &&
          suffix.all (choiceFieldsOnly ctx.types binding types view) then
        return { binding := view, params := [], instances := types.map fun _ => [] }
  return plan

def joinedChoiceResult (ctx : Ctx) (plan : ChoiceTypes.Plan) (lift : Choice.FirstLift) : EM Choice.FirstLift := do
  let own ← resolveTy ctx.types lift.pos lift.ret
  let some joined := choiceResultType ctx.types (plan.instances.map (own.subst ·))
    | eerr lift.pos "the alternatives have ambiguous result types"
  return { lift with joinedRet := if joined == own then none else some joined.toSTy }


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
  -- (#351: through views, only the classes that can be the object, as a
  -- read; typed even when none can)
  let viewedSn := env.viewed.contains sn
  if viewedSn then refined := true
  for (d, kd) in (ds.zip pos).reverse do
    if viewedSn && (env.viewArgs? sn d (env.coreArgs sn targs) (rigid := false)).isNone then continue
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

end OpenVerse.Front
