/- Elaboration of applications, `F(…)` and `F[…]`: each kind a function of
   its own, and `elabAppBaseWith`, the list of the kinds in the order they
   are tried. Public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Builtins
import OpenVerse.Front.TypeValues
import OpenVerse.Front.FinalSuper

namespace OpenVerse.Front
open OpenVerse

/-- The expression elaborator's entry points that an application's
    elaboration calls back into (`elabAppBase`, `Elab/Expr.lean`, passes
    them: they are defined after this file). -/
structure AppElab where
  elabE : Ctx → SExpr → Option Ty → EM R
  withDeferMark : Ctx → Expr → EM Expr
  elabSpawn : Ctx → Pos → SExpr → EM R
  resolveOverload : Ctx → Pos → String → List String → (String → Option Sig) → (String → EM R) →
    List SExpr → EM R
  elabArgs : Ctx → Pos → List SExpr → List Ty → EM (List Expr)
  elabInts : Ctx → Pos → List SExpr → EM (List Expr)
  elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R
  elabCast : Ctx → Pos → String → List SExpr → Bool → EM R
  elabGenericCall : Ctx → Pos → Sig → List SExpr → Option Ty → EM R
  elabMethod : Ctx → Pos → R → String → List SExpr → Bool → EM R
  elabIndexLike : Ctx → Pos → R → List SExpr → Bool → EM R
  elabSpawnDispatch : Ctx → Pos → String → String → String → List SExpr → Option Ty → EM R
  elabDefaultDispatch : Ctx → Pos → String → List SExpr → Bool → Option Ty → EM R
  elabMember : Ctx → Pos → R → String → Option Ty → EM R

/-! ## Applications of a value, a conversion, a cast -/

/-- `V[…]`, `V(…)` of a value `V` (`source`, as written): an array or a map
    indexed, a tuple's element, a function value called (`elabIndexLike`).
    A type value is not a function. -/
partial def elabValueApp (cb : AppElab) (ctx : Ctx) (p : Pos) (source : SExpr) (value : R)
    (args : List SExpr) (bracket : Bool) : EM R := do
  if !ctx.typeOnly && ctx.isTypeValue source then
    let view ← match ctx.callableView source.pos value.ty with
      | .ok view => pure view
      | .error message => throw message
    if view.isSome then eerr source.pos "dummy type value cannot be an executable function"
  cb.elabIndexLike ctx p value args bracket

/-- `t(X)`: `X` converted to the type `t`, a value of a type that is a
    subtype of it, then of `t` (Book of Verse tests, Cast.versetest 57-87:
    `int(0)`, `void(0)`, `(?int)(option{0})`; an `int(0.0)` or a `c1(c0{})`
    is refused). -/
partial def elabConversionWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (p : Pos) (t : STy)
    (args : List SExpr) : EM R := do
  let ty ← resolveTy ctx.types p t
  let [a] := args | eerr p s!"a conversion to {ty.show} takes one value, of a type that is a subtype of {ty.show}"
  let r ← elabE ctx a (some ty)
  return ⟨← coerce a.pos r ty, ty⟩

/-- `(t)(X)`: a conversion to a type written as one, `(?int)(option{0})`;
    it cannot fail, so it has no brackets. -/
partial def elabWrittenConversion (cb : AppElab) (ctx : Ctx) (p : Pos) (t : STy)
    (args : List SExpr) (bracket : Bool) : EM R := do
  if bracket then eerr p "a conversion is written (t)(X), of a value of a type that is a subtype of t: it cannot fail"
  elabConversionWith cb.elabE ctx p t args

/-- Whether `t(X)` is a conversion to `t` by its name: a built-in type's, a
    struct's or an enum's that no function takes, called without brackets
    (Book of Verse tests, Cast.versetest 57-87: "Test infallible casts.
    These should produce a compile error if the argument type is not a
    subtype of the cast type"), as `T(X)` is for a class (`elabCast`). -/
def convertsByName (ctx : Ctx) (name : String) (bracket : Bool) : Bool :=
  !bracket && (ctx.sig? name).isNone && (ctx.types.overloads.lookup name).isNone &&
    (["int", "float", "logic", "char", "char32", "string", "void", "rational"].contains name ||
      ((ctx.types.structs.lookup name).isSome && !ctx.types.classes.contains name) ||
      (ctx.types.enums.lookup name).isSome)

/-- `age[X]` of a refinement type `age` (#136): `X`, of the type `age`
    refines, if it meets `age`'s conditions; failing otherwise. -/
partial def elabRefinementCast (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (p : Pos)
    (name : String) (base : Ty) (conds : List (String × Value)) (args : List SExpr) (bracket : Bool) :
    EM R := do
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

/-! ## Applications of a name -/

/-- A call of an extension method's function `name`, `$ext:M` (Book of
    Verse ch. 6), which the modules' pass made of a call `X.M(…)` as
    `$ext:M(X, …)`: `X` is evaluated once, before the arguments, and when
    its type has a member `M` of its own (`Ctx.hasOwnMember`), the call is
    the one of the two it fits, refused as ambiguous when it fits both, as
    two overloads would be. A bare call `M(…)` in a method, made
    `$ext:M($implicitSelf:F, …)`, is the extension method's call with `Self`
    or `F(…)` as written, whichever it fits, and ambiguous when it fits
    both. `none`: an ordinary call of the function from here on (its
    receiver taken, or of no type of its own, as `array{}`, then taken at
    the parameter's type). -/
partial def elabExtensionCallWith
    (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (ctx : Ctx) (p fp : Pos) (name : String) (args : List SExpr) (bracket : Bool)
    (exp : Option Ty) : EM (Option R) := do
  let (some m, recv :: rest) := (extensionMethod? name, args) | return none
  let fits (call : EM R) : EM Bool := do
    let st ← get
    let ok ← tryCatch (do discard call; pure true) (fun _ => pure false)
    set st
    return ok
  if let .ident ip n := recv then
    if n.startsWith implicitSelfPrefix then
      let written := elabApp ctx p (.ident ip (n.drop implicitSelfPrefix.length).toString) rest bracket exp
      let withSelf := elabApp ctx p (.ident fp name) (.ident ip "Self" :: rest) bracket exp
      if !(← fits withSelf) then return some (← written)
      if ← fits written then
        eerr p s!"this call of {m} is ambiguous: it fits {m} as written, and the extension method {m} with Self as its receiver (Book of Verse ch. 6)"
      return some (← withSelf)
    if n.startsWith "$extReceiver" then return none
  if ← argNeedsTypeWith elabE ctx recv then return none
  let r ← elabE ctx recv none
  let slot ← fresh r.ty
  let rn := s!"$extReceiver{slot}"
  let ctx' := { ctx with locals := { name := rn, slot, ty := r.ty, mutable := false,
                                     typeValue := ctx.isTypeValue recv } :: ctx.locals }
  let extCall := elabApp ctx' p (.ident fp name) (.ident fp rn :: rest) bracket exp
  let memberCall := elabApp ctx' p (.member fp (.ident fp rn) m) rest bracket exp
  let rc ← if !ctx.hasOwnMember fp r.ty m then extCall
    else if !(← fits extCall) then memberCall
    else if ← fits memberCall then
      eerr p s!"this call of {m} is ambiguous: {r.ty.show}'s own {m} and the extension method {m} both take it (Book of Verse ch. 6)"
    else extCall
  return some ⟨.seq (.assign slot r.e) rc.e, rc.ty⟩

/-- `L(…)`, `L[…]` of a local `L`: with `L` a type value of `subtype(A)` or
    its kin, `L[X]` is `X` cast through it, `L.$cast(A)[A[X]]`
    (`TypeValues`); otherwise `L`'s value indexed or called. -/
partial def elabLocalApp (cb : AppElab) (ctx : Ctx) (p : Pos) (f : SExpr) (name : String) (l : Local)
    (args : List SExpr) (bracket : Bool) (exp : Option Ty) : EM R := do
  if let .struct iface [] := l.ty then
    if let some (_, a) := TypeValues.bound? iface then
      let [x] := args | eerr p s!"a cast through {name} takes one value"
      if !bracket then eerr p s!"a cast through the type {name} can fail: write {name}[X]"
      -- (`subtype(int)`'s values are types other than classes, whose
      -- interface has no cast, `TypeValues`)
      if !ctx.hasMethod iface (TypeValues.castMethod a) then
        eerr p s!"a cast through {name}, of type {iface}, would cast to {a}, which is no class or interface: a cast is to a class or an interface (Book of Verse ch. 11)"
      return ← cb.elabApp ctx p (.member p f (TypeValues.castMethod a)) [.app p (.ident p a) [x] true] true exp
  elabValueApp cb ctx p f ⟨.local l.slot, l.ty⟩ args bracket

/-- Whether `F(…)` in a method is `Self.F(…)`: `F` is a method of `Self`
    (or an overloaded one, #106), or a field of `Self`, indexed, that has
    no built-in function's name. -/
def callsSelfMember (ctx : Ctx) (name : String) : Bool :=
  match ctx.selfClass with
  | some c => ctx.hasMethod c name ||
      ((ctx.types.methodOverloads.lookup name).map (·.any (ctx.hasMethod c ·))).getD false ||
      ((ctx.types.fields c).any (·.1 == name) && !builtins.contains name && !softBuiltins.contains name)
  | none => false

/-- `F(…)` of an overloaded function `F` (`ovs`, its overloads): the one the
    call fits (`resolveOverload`), then a call of it. -/
partial def elabOverloadedCall (cb : AppElab) (ctx : Ctx) (p : Pos) (name : String) (ovs : List String)
    (args : List SExpr) (bracket : Bool) (exp : Option Ty) : EM R :=
  cb.resolveOverload ctx p name ovs ctx.sig? (fun o => do
    ctx.noteOverload p name o
    cb.elabApp ctx p (.ident p o) args bracket exp) args

/-- A call's own code marks where it suspends: a call of a `<suspends>`
    function records the defers active there (#156). -/
def markSuspension (cb : AppElab) (ctx : Ctx) (s : Sig) (e : Expr) : EM Expr :=
  if s.suspends then cb.withDeferMark ctx e else pure e

/-- Whether an argument is named, `?X := V`. -/
def isNamedArgument : SExpr → Bool
  | .decl _ n _ _ _ => n.startsWith "?"
  | _ => false

/-- `F(A, B, …)` of a function `F` (`s`) with positional arguments only: one
    tuple for several parameters is expanded into them (Book of Verse ch. 3:
    `Describe(MyTuple)` is `Describe(1, "two")`), several arguments for one
    array parameter make the array (`Sum(1, 2, 3, 4)`, as a tuple converts
    to an array), and otherwise each argument is its parameter's. -/
partial def elabPositionalCall (cb : AppElab) (ctx : Ctx) (p : Pos) (name : String) (s : Sig)
    (args : List SExpr) : EM R := do
  if args.length == 1 && s.params.length > 1 then
    for k in List.range s.params.length do ctx.checkArgumentRole s args[0]! k
  else
    for (argument, index) in args.zipIdx do
      ctx.checkArgumentRole s argument (if s.params.length == 1 then 0 else index)
  if let [a] := args then
    if s.params.length > 1 then
      let r ← cb.elabE ctx a (some (.tup s.params))
      if let .tup ts := r.ty then
        if ts.length == s.params.length then
          let tt ← fresh r.ty
          -- (an element that never gives a value left before the
          -- call: `Err()` in its place, of every type, #290)
          let parts ← ((s.params.zip ts).zip (List.range ts.length)).mapM fun ((pt, et), i) =>
            if et == .never then pure (.prim .userErr [])
            else coerce a.pos ⟨.prim (.tupGet i) [.local tt], et⟩ pt
          return ⟨← markSuspension cb ctx s (.seq (.assign tt r.e) (.call s.idx parts)), s.ret⟩
      let (shown, off) := match name.splitOn "." with
        | [_, m] => if s.pnames.head? == some "Self" then (m, 1) else (name, 0)
        | _ => (name, 0)
      eerr p s!"{shown} takes {s.params.length - off} argument(s), found 1 (of type {r.ty.show})"
  if let [.arr et] := s.params then
    if args.length > 1 then
      let es ← cb.elabArgs ctx p args (args.map fun _ => et)
      return ⟨← markSuspension cb ctx s (.call s.idx [.prim .mkArr es]), s.ret⟩
  let es ← cb.elabArgs ctx p args s.params
  return ⟨← markSuspension cb ctx s (.call s.idx es), s.ret⟩

/-- `F(A, ?X := V, …)` of a function `F` (`s`) with named parameters:
    positional arguments evaluated left to right, then named ones as
    written, then the defaults of those omitted (Book of Verse §2.5), into
    temporaries. A default sees the parameters before it, and a method's its
    receiver's fields; it is elaborated in a context of its own (no `return`
    or `break` into the caller, failure only for a `<decides>` callee, and
    not its own default again). -/
partial def elabNamedArgsCall (cb : AppElab) (ctx : Ctx) (p : Pos) (name : String) (s : Sig)
    (args : List SExpr) : EM R := do
  let npos := s.params.length - s.named.length
  let pos := args.filter (!isNamedArgument ·)
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
    ctx.checkArgumentRole s a k
    let t := ptys[k]!
    let ta ← fresh t
    steps := steps.push (.assign ta (← coerce a.pos (← cb.elabE ctx a (some t)) t))
    slots := slots.set! k (some ta)
  for (ap, n, rhs) in named do
    let k := npos + (s.named.findIdx? (·.1 == n)).get!
    ctx.checkArgumentRole s rhs k
    let t := ptys[k]!
    let ta ← fresh t
    steps := steps.push (.assign ta (← coerce ap (← cb.elabE ctx rhs (some t)) t))
    slots := slots.set! k (some ta)
  for ((n, dflt), j) in s.named.zip (List.range s.named.length) do
    let k := npos + j
    if slots[k]!.isNone then
      let some d := dflt | eerr p s!"{name} needs the argument ?{n}, which has no default"
      let t := ptys[k]!
      let ta ← fresh t
      -- (the default sees the parameters before it, in their temporaries)
      let earlier : List Local := ((s.pnames.zip (List.range k)).filterMap fun (pn, j) =>
        (slots[j]!).map fun sl => ({ name := pn, slot := sl, ty := ptys[j]!, mutable := false, typeValue := s.typeValues.contains j } : Local)).reverse
      -- (a method's: its receiver's fields too, through `Self`; a
      -- copy's in its interface's scope, as its body, #53)
      let selfC : Option String :=
        if s.pnames.head? == some "Self" then (s.name.splitOn ".").head? else none
      -- (its own context: no return or break into the caller, failure
      -- only for a <decides> callee, and not its own default again)
      let key := (s.name, s!"?{n}")
      if ctx.defaults.contains key then
        eerr p s!"the default of ?{n} of {name} uses itself (a call of {name} that omits ?{n})"
      let dctx := { ctx with locals := earlier, selfClass := selfC,
                             selfMethod := if selfC.isSome then (s.name.splitOn ".").getLast? else none,
                             inParamDefault := true,
                             inLoop := false, canFail := ctx.canFail && s.decides,
                             inRollback := ctx.inRollback || ctx.canFail,
                             suspends := ctx.suspends && s.suspends,
                             defaults := key :: ctx.defaults }
      dctx.checkArgumentRole s d k
      let rd ← fxAt p (do coerce p (← cb.elabE dctx d (some t)) t)
      if !s.decides && rd.mayFail ctx.sigProg then
        eerr p s!"the default of ?{n} of {name} can fail, but {name} is not <decides>"
      steps := steps.push (.assign ta rd)
      slots := slots.set! k (some ta)
  let call := Expr.call s.idx (slots.toList.map fun o => Expr.local o.get!)
  let e := steps.toList.foldr Expr.seq call
  return ⟨← markSuspension cb ctx s e, s.ret⟩

/-- `F(…)`, `F[…]` of the program's function `F`, or of its constant `F`,
    whose value is then indexed or called: the call has its callee's
    effects, and brackets exactly when the callee is `<decides>` (Book of
    Verse §8.1); a `<suspends>` callee only where a call may suspend (#156);
    then a generic call (`elabGenericCall`), one with positional arguments
    or one with named ones. `Sleep` is the concurrency helpers' unless the
    program has its own (#156). Refused: a call of an abstract class's
    constructor, and of an unknown function. -/
partial def elabFunctionCall (cb : AppElab) (ctx : Ctx) (p : Pos) (f : SExpr) (name : String)
    (args : List SExpr) (bracket : Bool) (exp : Option Ty) : EM R := do
  let name := if name == "Sleep" && (ctx.sig? "Sleep").isNone then "$Sleep" else name
  if name == "$Sleep" && (ctx.sig? name).isNone then
    eerr p "Sleep suspends: it can only be called in a <suspends> function (#156)"
  match ctx.sig? name with
  | some s =>
    -- a call has its callee's effects
    -- (a built-in's call that the front end wrote as its helper's names
    -- the built-in, `FinalSuper.calledBy?`)
    noteFx p s.fx (some (if s.isConst then s!"uses the constant {name}" else s!"calls {(FinalSuper.calledBy? name).getD name}"))
    if s.isConst then
      elabValueApp cb ctx p f ⟨.call s.idx [], s.ret⟩ args bracket
    else
      let args := packCallArgs p s args
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
        let r ← cb.elabGenericCall ctx p s args exp
        if s.suspends then return ⟨← cb.withDeferMark ctx r.e, r.ty⟩ else return r
      if s.named.isEmpty && !args.any isNamedArgument then
        elabPositionalCall cb ctx p name s args
      else elabNamedArgsCall cb ctx p name s args
  | none =>
    if (ctx.sig? s!"{name}$init").isSome || (ctx.types.overloads.lookup s!"{name}$init").isSome then
      eerr p s!"{name} constructs an abstract class: it can only be delegated to, as {name}<constructor>(…) in a constructor of a class below it"
    -- (`weak_map(k, v)` is a type, the API reference's "It appears where a
    -- type is expected rather than where a value is")
    if name == "weak_map" then
      eerr p "weak_map(…) is a type, not a function: a type as a value is supported for classes and interfaces (Types as values), and a type alias is a definition of its own, t := weak_map(k, v)"
    eerr p s!"unknown function '{name}'"

/-! ## Applications of a member -/

/-- `(super:)M(…)`: the implementation of `M` the current method's class
    inherits; of an overloaded `M` (#106), the overload above the class the
    call fits. -/
partial def elabSuperCall (cb : AppElab) (ctx : Ctx) (p mp : Pos) (m : String) (args : List SExpr)
    (bracket : Bool) (exp : Option Ty) : EM R := do
  let some c := ctx.selfClass | eerr p "(super:) can only be used in a method"
  if let some ms := (if (ctx.methodDecl? c m).isNone then ctx.types.methodOverloads.lookup m else none) then
    -- (the overloads above `c`)
    let above := (ctx.types.supers c).drop 1
    let declAbove (o : String) : Option String := above.find? fun e => (ctx.sig? s!"{e}.{o}").isSome
    let sigOf (o : String) : Option Sig := (declAbove o).bind fun owner =>
      (ctx.sig? s!"{owner}.{o}").map fun sg => { sg with params := sg.params.drop 1 }
    let vis := ms.filter fun o => (declAbove o).isSome
    if !vis.isEmpty then
      return ← cb.resolveOverload ctx p m vis sigOf (fun o => do
        ctx.noteOverload p m o
        cb.elabApp ctx p (.member mp (.ident mp "(super:)") o) args bracket exp) args
  ctx.noteOverload p m m
  let impl ← superImpl ctx p c m
  cb.elabApp ctx p (.ident mp impl) (.ident mp "Self" :: args) bracket exp

/-- `X.Await()`, `X.Cancel()`, `X.Signal()` of a value of a type parameter
    whose bound gives it the method (`Ctx.concurrencyView`): the call
    through `X` converted to that type. `none`, with nothing elaborated,
    for any other call. -/
partial def elabParamConcurrencyCall? (cb : AppElab) (ctx : Ctx) (p mp : Pos) (obj : SExpr) (m0 : String)
    (spawning : Bool) (args : List SExpr) (bracket : Bool) (exp : Option Ty) : EM (Option R) := do
  if !(args.isEmpty && ["Await", "Cancel", "Signal"].contains m0) then return none
  let before ← get
  let receiver ← cb.elabE ctx obj none
  if let .param .. := receiver.ty then
    let view ← match ctx.concurrencyView mp receiver.ty m0 with
      | .ok view => pure view
      | .error message => throw message
    if let some target := view then
      let converted ← elabArgumentCoerceWith cb.elabE ctx mp receiver target
      let slot ← fresh target
      let name := s!"$concurrencyReceiver{slot}"
      let binding : Local := {
        name, slot, ty := target, mutable := false, typeValue := ctx.isTypeValue obj }
      let inner := { ctx with locals := binding :: ctx.locals }
      let method := if spawning then "$spawnMethod:" ++ m0 else m0
      let result ← cb.elabApp inner p (.member mp (.ident mp name) method) args bracket exp
      return some ⟨.seq (.assign slot converted) result.e, result.ty⟩
  set before
  return none

/-- `T.Cancel()` of a task (#156): the mark `$cancelMark(T)`, which the
    lowering turns into the cancellation of the task's root; only where a
    call may suspend. `none` for any other call (its receiver is
    elaborated). -/
partial def elabTaskCancel? (cb : AppElab) (ctx : Ctx) (p : Pos) (obj : SExpr) (m0 : String)
    (args : List SExpr) : EM (Option R) := do
  if !(m0 == "Cancel" && args.isEmpty) then return none
  let rt ← cb.elabE ctx obj none
  if let .struct n [_] := rt.ty then
    if n == ctx.types.concurrencyName "task" then
      if !ctx.suspends then eerr p "Cancel suspends: it can only be called in a <suspends> function (#156)"
      if ctx.inDefer then eerr p "Cancel suspends, and a defer cannot suspend (#156)"
      if ctx.canFail then eerr p "Cancel suspends, and a failure context (a condition, a filter, or a <decides> call's arguments) cannot (#156)"
      let some mark := ctx.sig? "$cancelMark" | eerr p "internal error: no Cancel helper"
      let t ← fresh rt.ty
      return some ⟨.seq (.assign t rt.e) (.call mark.idx [.local t]), .void⟩
  return none

/-- `E.Signal()` of an `event()` (#156): `E.Signal(())`, with the value
    `void`. `none` for any other call (its receiver is elaborated). -/
partial def elabEventSignal? (cb : AppElab) (ctx : Ctx) (p mp : Pos) (obj : SExpr) (m0 : String)
    (args : List SExpr) (bracket : Bool) (exp : Option Ty) : EM (Option R) := do
  if !(m0 == "Signal" && args.isEmpty) then return none
  match (← cb.elabE ctx obj none).ty with
  | .struct n ts =>
    if ((n == ctx.types.concurrencyName "event" || n == ctx.types.concurrencyName "sticky_event") &&
        ts == [.void]) || (n == "$subev0" && ts.isEmpty) then
      return some (← cb.elabApp ctx p (.member mp obj "Signal") [.tuple p []] bracket exp)
    else return none
  | _ => return none

/-- `T.Await()` of a task, and `E.Await()` of an event (#156): the helper
    `$Await(T)`, `$EvAwait(E)` or, of a sticky event, `$StickyAwait(E)`.
    `none` for any other call (its receiver is elaborated). -/
partial def elabAwait? (cb : AppElab) (ctx : Ctx) (p mp : Pos) (obj : SExpr) (m0 : String)
    (args : List SExpr) (exp : Option Ty) : EM (Option R) := do
  if !(m0 == "Await" && args.isEmpty) then return none
  match (← cb.elabE ctx obj none).ty with
  | .struct n ts =>
    if n == ctx.types.concurrencyName "task" && ts.length == 1 then
      return some (← cb.elabApp ctx p (.ident mp "$Await") [obj] false exp)
    else if ((n == ctx.types.concurrencyName "event" || n == ctx.types.concurrencyName "subscribable_event") &&
        ts.length == 1) || (n == "$subev0" && ts.isEmpty) then
      return some (← cb.elabApp ctx p (.ident mp "$EvAwait") [obj] false exp)
    else if n == ctx.types.concurrencyName "sticky_event" && ts.length == 1 then
      return some (← cb.elabApp ctx p (.ident mp "$StickyAwait") [obj] false exp)
    else return none
  | _ => return none

/-- `X.(i:)M(…)`: `X` as an `i`, so `i`'s `M` (a qualified call); a
    qualifier names where the method is, the class or interface that
    introduces it, not one that inherits or overrides it (Book of Verse
    tests, SOL-3564-CallingSuperClassMethodFromOverriddenMethod). Any other
    call keeps its receiver and method. -/
partial def qualifiedReceiver (ctx : Ctx) (p : Pos) (r0 : R) (m0 : String) : EM (R × String) := do
  match r0.ty, m0.startsWith "(", (m0.drop 1).toString.splitOn ":)" with
  | .struct c ts, true, [q, mq] =>
    if !(ctx.types.isSub c q) then eerr p s!"{c} is not below {q}"
    if (ctx.methodDecl? q mq).isSome && !(ctx.rootsOf q mq).contains q then
      let roots := ctx.rootsOf q mq
      eerr p s!"X.({q}:){mq}: {q} does not introduce {mq}, it {if (ctx.sig? s!"{q}.{mq}").isSome then "overrides" else "inherits"} it: a qualifier names where the method is defined, {" or ".intercalate (roots.map fun r => s!"({r}:)")}"
    -- (converted: a receiver of a type with no instance is unreachable)
    let qt : Ty := .struct q (ctx.types.upArgs c ts q)
    pure (⟨← coerce p r0 qt, qt⟩, mq)
  | _, _, _ => pure (r0, m0)

/-- `X.M(…)` of a method `M` overloaded (#106) at the class `c` of `X`: the
    overload visible at `c` the call fits, then a call of that method (a
    qualified call stays qualified, `X.(q:)M$ovK(…)`, #125). `none` when `M`
    is not overloaded at `c` or no overload of it is visible there. -/
partial def elabOverloadedMethodCall? (cb : AppElab) (ctx : Ctx) (p mp : Pos) (obj : SExpr) (c m m0 : String)
    (spawning : Bool) (args : List SExpr) (bracket : Bool) (exp : Option Ty) : EM (Option R) := do
  let env := ctx.types
  let some ms := (if env.classes.contains c && (ctx.methodDecl? c m).isNone then
      env.methodOverloads.lookup m else none) | return none
  let sigOf (o : String) : Option Sig := (ctx.methodDecl? c o).bind fun owner =>
    (ctx.sig? s!"{owner}.{o}").map fun sg => { sg with params := sg.params.drop 1 }
  let vis := ms.filter fun o => (ctx.methodDecl? c o).isSome
  let qualOf (o : String) : String :=
    if m0.startsWith "(" then
      match (m0.drop 1).toString.splitOn ":)" with
      | [q, _] => s!"({q}:){o}"
      | _ => o
    else o
  if vis.isEmpty then return none
  return some (← cb.resolveOverload ctx p m vis sigOf (fun o => do
    ctx.noteOverload p m o
    cb.elabApp ctx p (.member mp obj ((if spawning then "$spawnMethod:" else "") ++ qualOf o)) args bracket exp) args)

/-! ## A call of a class's or interface's method through a value -/

/-- A call `X.M(…)` of a class's or interface's method `m` through a value
    of `c(targs)`, checked, before an implementation is chosen: what each
    way of calling it reads. -/
structure MethodCall where
  /-- the receiver's class or interface and its type arguments -/
  c : String
  targs : List Ty
  /-- the method, the class or interface that declares it, and the root of
      the slots the call covers (#70) -/
  m : String
  owner : String
  root : String
  /-- the method's signature, as declared (its receiver first) -/
  ms : Sig
  /-- the receiver, which is evaluated first, into `slot` -/
  recv : R
  slot : Nat
  obj : SExpr
  /-- the classes the receiver's object can be of -/
  ds : List String
  mp : Pos
  /-- a call `spawn{X.M(…)}` -/
  spawning : Bool
  /-- the arguments, packed (`packCallArgs`) -/
  args : List SExpr
  bracket : Bool
  exp : Option Ty

/-- The class or interface an implementation `e.M` is of. -/
def implClass (fname : String) : String := (fname.splitOn ".").head!

/-- The receiver's type arguments as an instance of class `e`, above or
    below `c` (#39). -/
def MethodCall.argsAt (env : TyEnv) (mc : MethodCall) (e : String) : List Ty :=
  if env.isSub mc.c e then env.upArgs mc.c mc.targs e else env.argsBelow mc.c mc.targs e

/-- The implementation a call can name directly: the one every class below
    the receiver's type has, when it is at or above that type (#351: at an
    interface referred to through views, only when the receiver converts to
    it; otherwise each class's test, which a class's pins refine by, `i1(t)`
    as an `i1(char)`). -/
def directImplementation? (ctx : Ctx) (mc : MethodCall) : Option String :=
  let env := ctx.types
  match (mc.ds.map (ctx.implFor? · mc.root mc.m)).eraseDups with
  | [some fname] =>
    let e := implClass fname
    if !env.isSub mc.c e then none
    else if env.viewed.contains e && !env.viewed.contains mc.c && mc.c != e then
      match env.viewFits (.struct mc.c mc.targs) (.struct e (if env.isSub mc.c e then env.upArgs mc.c mc.targs e else [])) with
      | some (_, false) => none
      | _ => some fname
    else some fname
  | _ => none

/-- A direct call of the implementation `fname` (`directImplementation?`),
    the receiver evaluated first, as `Self` (#351: at an interface referred
    to through views, the receiver converted to it, in a slot of its type:
    a reference through a prefix one is no reference through views without
    it); spawned for `spawn{X.M(…)}`. -/
partial def elabDirectMethodCall (cb : AppElab) (ctx : Ctx) (p : Pos) (mc : MethodCall) (fname : String) :
    EM R := do
  let env := ctx.types
  let e := implClass fname
  let (pre, eslot) ← if env.viewed.contains e && !env.viewed.contains mc.c && mc.c != e then do
      let es ← fresh (.struct e (mc.argsAt env e))
      pure ([Expr.assign es (← coerce p ⟨.local mc.slot, mc.recv.ty⟩ (.struct e (mc.argsAt env e)))], es)
    else pure ([], mc.slot)
  let recv := s!"$recv{mc.slot}"
  let ctx' := { ctx with
    locals := { name := recv, slot := eslot, ty := .struct e (mc.argsAt env e), mutable := false, typeValue := ctx.isTypeValue mc.obj } :: ctx.locals }
  let rc ← if mc.spawning then
      cb.elabSpawn ctx' p (.app p (.ident mc.mp fname) (.ident mc.mp recv :: mc.args) mc.bracket)
    else cb.elabApp ctx' p (.ident mc.mp fname) (.ident mc.mp recv :: mc.args) mc.bracket mc.exp
  return ⟨.seq (.assign mc.slot mc.recv.e) (pre.foldr Expr.seq rc.e), rc.ty⟩

/-- The arguments of a dispatched call, evaluated before the dispatch, and
    the method's result type at the call. -/
structure DispatchArgs where
  /-- the receiver's and the arguments' evaluation into temporaries, in
      order -/
  pre : Array Expr
  /-- the temporaries, as locals -/
  locs : List Local
  /-- the arguments every implementation is called with, those
      temporaries -/
  argIds : Array SExpr
  /-- the method's result type at the receiver's type arguments and the
      method's own -/
  msRet : Ty

/-- The arguments of a dispatched call, once each: positional ones left to
    right, then named ones as written (Book of Verse §2.5), passed to every
    implementation; those omitted take the default of the implementation
    that runs, as in a call without named arguments. The method's own type
    parameters are inferred from the expected result type (unless void),
    then from the arguments, as for a generic call: an argument is checked
    against its parameter's type once the own type parameters it mentions
    are bound, else inferred from; `false`, `array{}` and `map{}` take their
    type from context, so they wait for the others (they are still
    evaluated in order). -/
partial def dispatchArgs (cb : AppElab) (ctx : Ctx) (p : Pos) (mc : MethodCall) : EM DispatchArgs := do
  let env := ctx.types
  let { m, owner, ms, recv := r, slot, obj, mp, args, exp, .. } := mc
  let ownerTps := ((env.sparams.lookup owner).getD []).map (·.1)
  -- the declaration's types at the receiver's type arguments, its own
  -- type parameters renamed apart (they are inferred from the
  -- arguments below, as for a generic call)
  let ownTps := ms.tparams.drop ownerTps.length
  let ownσ : List (String × Ty) := (ownTps.zip (List.range ownTps.length)).map fun ((v, k), i) =>
    (v, Ty.param s!"$own{i}" k)
  let ownNames := (List.range ownTps.length).map fun i => s!"$own{i}"
  let σ := ownerTps.zip (mc.argsAt env owner)
  let declTy (t : Ty) : Ty := (t.subst ownσ).subst σ
  let mut σu : List (String × Ty) := []
  let posArgs := args.filter (!isNamedArgument ·)
  let namedArgs := args.filterMap fun a => match a with
    | .decl ap n _ _ rhs => if n.startsWith "?" then some (ap, (n.drop 1).toString, rhs) else none
    | _ => none
  let npos := ms.params.length - ms.named.length
  if posArgs.length + 1 != npos then
    eerr p s!"{m} takes {npos - 1} positional argument(s), found {posArgs.length}"
  for (ap, n, _) in namedArgs do
    if (ms.named.find? (·.1 == n)).isNone then eerr ap s!"{m} has no parameter ?{n}"
  let mut pre : Array Expr := #[.assign slot r.e]
  let mut locs : List Local := [{ name := s!"$recv{slot}", slot, ty := r.ty, mutable := false, typeValue := ctx.isTypeValue obj }]
  let mut argIds : Array SExpr := #[]
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
  let contextual := (← given.mapM (fun (a, _, _) => argNeedsTypeWith cb.elabE ctx a)).toArray
  let mut done : Array (Option (Expr × Ty)) := Array.replicate given.length none
  let mut deferred : Array Bool := contextual
  for pass in [0, 1] do
    for ((a, t0, _), i) in given.zipIdx do
      if (pass == 0) == deferred[i]! then continue
      let t := (declTy t0).subst σu
      if t.params.any ownNames.contains then
        let cannot := s!"cannot infer the type parameters of {m} from the arguments of this call"
        if contextual[i]! && !a.typedAlone then eerr a.pos cannot
        let r ← cb.elabE ctx a none
        match ctx.matchArgument σu t r.ty with
        | some σ' =>
          σu := own? σ'
          let t' := t.subst σu
          if t'.params.any ownNames.contains then
            if pass == 0 then deferred := deferred.set! i true
            else eerr a.pos s!"cannot infer the type parameters of {m} from this argument"
          else done := done.set! i (some (← elabArgumentCoerceWith cb.elabE ctx a.pos r t', t'))
        | none => eerr a.pos (if contextual[i]! then cannot else s!"expected {showT t}, found {r.ty.show} (in a call of {m})")
      else
        done := done.set! i (some (← coerce a.pos (← cb.elabE ctx a (some t)) t, t))
  let mut namedSlots : List (String × Nat) := []
  for ((argument, _, name), d) in given.zip done.toList do
    let some (e, t) := d | eerr p s!"cannot infer the type parameters of {m} from the arguments of this call"
    let ta ← fresh t
    pre := pre.push (.assign ta e)
    locs := { name := s!"$arg{ta}", slot := ta, ty := t, mutable := false, typeValue := ctx.isTypeValue argument } :: locs
    match name with
    | none => argIds := argIds.push (.ident mp s!"$arg{ta}")
    | some n => namedSlots := namedSlots ++ [(n, ta)]
  for (n, ta) in namedSlots do
    argIds := argIds.push (.decl mp s!"?{n}" none false (.ident mp s!"$arg{ta}"))
  let msRet := (declTy ms.ret).subst σu
  if msRet.params.any ownNames.contains then
    eerr p s!"cannot infer the type parameters of {m} from the arguments of this call"
  return { pre, locs, argIds, msRet }

/-- `spawn{X.M(…)}` dispatched: the arguments cannot suspend (#156); for
    each class the object can be of, the factory of its implementation's
    task (`elabSpawnDispatch`), called on the test of the object's class. -/
partial def elabSpawnMethodDispatch (cb : AppElab) (ctx : Ctx) (p : Pos) (mc : MethodCall)
    (da : DispatchArgs) : EM R := do
  let env := ctx.types
  let slot := mc.slot
  let isS (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.suspends
  let skip (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.name == "$spawnMark"
  if da.pre.any (fun e => Suspend.countSusp isS (fun _ => false) false skip e > 0) then
    eerr p "the arguments of a spawned call cannot suspend (#156)"
  let taskTy := Ty.struct (ctx.types.concurrencyName "task") [da.msRet]
  let rargs := env.coreArgs mc.c mc.targs
  let mut acc : Expr := .prim .userErr []
  for d in mc.ds.reverse do
    let some fname := ctx.implFor? d mc.root mc.m | eerr p s!"class {d} does not implement '{mc.m}'"
    let vars := env.coreVars d
    let X := vars.zipIdx.map fun ((_, t), i) =>
      Ty.param s!"$ext{i}" (match t with | .param _ k => k | _ => false)
    let view := if env.viewed.contains mc.c then env.viewOf mc.c d X else X.take rargs.length
    let atX := X.zipIdx.map fun (x, j) => (pinArg j, x)
    let pins := (X.zip (env.dispatchPins d)).filterMap fun (x, pin) =>
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
      locals := self :: (da.locs ++ ctx.locals).map (fun l => { l with ty := l.ty.subst mu }),
      types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst mu) }, unrefine }
    let rc ← cb.elabSpawnDispatch cctx p d fname s!"{mc.owner}.{mc.m}" (.ident p name :: da.argIds.toList)
      (some (taskTy.subst mu))
    match rc.e with
    | .prim .userErr [] => continue -- factory discovery; no task or wait yet
    | _ => pure ()
    let some (.call fi (.local receiver :: values)) := Expr.inlineArgTemps rc.e
      | eerr p "internal: a spawn factory is not a dispatch call"
    if receiver != slot then eerr p "internal: a spawn factory changed its receiver"
    acc := .ite (.heap (.isTag [env.tagOf d]) [.local slot]) (.call fi (.local slot :: values)) acc
  let result ← fresh taskTy
  return ⟨da.pre.toList.foldr Expr.seq (.assign result acc), taskTy⟩

/-- A call through a reference to an interface referred to through views
    (#351): one test per class below, a dispatch that opens the class's
    Verse Core type arguments, refined by its view (the receiver's are the
    interface's at the class's) and its pins (`Typed.dispatch_view`). -/
partial def elabViewDispatch (cb : AppElab) (ctx : Ctx) (p : Pos) (mc : MethodCall) (da : DispatchArgs) :
    EM R := do
  let env := ctx.types
  let slot := mc.slot
  let mut acc : Expr := .prim .userErr []   -- no option set: unreachable
  let rargs := env.coreArgs mc.c mc.targs
  let mut emitted := false
  for d in mc.ds.reverse do
    let some fname := ctx.implFor? d mc.root mc.m | eerr p s!"class {d} does not implement '{mc.m}'"
    let e := implClass fname
    let vars := env.coreVars d
    -- (each as comparable as the type parameter at its place)
    let X := vars.zipIdx.map fun ((_, t), i) =>
      Ty.param s!"$ext{i}" (match t with | .param _ k => k | _ => false)
    let view := env.viewOf mc.c d X
    let atX := X.zipIdx.map fun (x, j) => (pinArg j, x)
    let pinEqs := (X.zip (env.dispatchPins d)).filterMap fun (x, pin) => match pin with
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
    let locsF := da.locs.map fun l => { l with ty := l.ty.subst μF }
    let selfL : Local := { name := selfName, slot,
                           ty := .struct e (eArgs.map (·.subst μF)), mutable := false }
    let unrefine := μF.filterMap fun (x, t) =>
      if ctx.dictVars.contains x && t.params.any (·.startsWith "$ext") then
        (ctx.types.tvars.lookup x).map (t, ·)
      else none
    let ctx' := { ctx with
      locals := selfL :: (locsF ++ ctx.locals.map fun l => { l with ty := l.ty.subst μF }),
      types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst μF) }, unrefine }
    let rc ← cb.elabDefaultDispatch ctx' p fname (.ident mc.mp selfName :: da.argIds.toList) mc.bracket
      (some (da.msRet.subst μF))
    let rcE : Expr := match rc.e with
      | .seq (.ite (.prim .fail []) _ (.lit .void)) b => b
      | e => e
    -- (a dispatch through a view opens all of the class's type
    -- arguments: defaults with no type of their own at the
    -- declaration's, #209)
    let some (.call fi (.local s0 :: es)) := Expr.inlineArgTemps rcE
      | eerr p s!"cannot dispatch {mc.m} through a view to class {d} yet when a named argument's default is computed (#351)"
    if s0 != slot then eerr p s!"internal error: a dispatch through a view to class {d} (#351)"
    acc := .ite (.heap (.isTag [env.tagOf d]) [.local slot]) (.call fi (.local slot :: es)) acc
    emitted := true
  if !emitted && mc.ms.decides then acc := .prim .fail []
  let y ← fresh da.msRet
  let body ← if mc.ms.suspends then cb.withDeferMark ctx (.assign y acc) else pure (.assign y acc)
  return ⟨da.pre.toList.foldr Expr.seq body, da.msRet⟩

/-- A call through a reference to a class or interface (#34): one test of
    the object's class per implementation. An implementation of a class
    that fixes type arguments the receiver's may not have (#142) is called
    under the refinement its pins give (`Typed.dispatch`), one test per set
    of pins (#209); one at or above the receiver's class takes the receiver
    as it is. With no class that can be the receiver, the call cannot run
    (a failable one still fails, for the failure checks). -/
partial def elabReferenceDispatch (cb : AppElab) (ctx : Ctx) (p : Pos) (mc : MethodCall) (da : DispatchArgs) :
    EM R := do
  let env := ctx.types
  let { c, targs, m, root, ms, slot, mp, bracket, exp, ds, .. } := mc
  let { pre, locs, argIds, msRet } := da
  let mut acc : Expr := .prim .userErr []   -- no option set: unreachable
  let mut groups : Array (String × Array String) := #[]
  for d in ds do
    let some fname := ctx.implFor? d root m | eerr p s!"class {d} does not implement '{m}'"
    match groups.findIdx? (·.1 == fname) with
    | some gi => groups := groups.modify gi fun (e', cls) => (e', cls.push d)
    | none => groups := groups.push (fname, #[d])
  let mut pinned := false
  let mut emitted := false
  for (fname, cls) in groups.toList.reverse do
    let e := implClass fname
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
    -- (#351: also one above it, the default of an interface referred
    -- to through views, when the receiver does not convert to it: a
    -- class's pins refine it, as Verse Core's are, `dispatchPins`)
    let viewedAbove := env.isSub c e && env.viewed.contains e && !env.viewed.contains c && c != e
    if !plainSusp && (!env.isSub c e || viewedAbove) && cls.any fun d =>
        !(needOf (env.dispatchPins d)).isEmpty || eLen > rargs.length then
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
        -- (#530: not an interface's default seen through views, which
        -- a test's temporary of its type cannot take as it is: a
        -- class whose closed view the receiver's do not give, `c1`'s
        -- `string` for `i1(u)`, is one only under the refinement)
        if calleeDicts != 0 && !viewedAbove &&
            !VTy.pinsBelow (env.lowerPins (pins.take (max eLen rargs.length))) (max eLen rargs.length) &&
            (needOf (env.corePins e)).isEmpty && eLen ≤ rargs.length then
          let argsE := mc.argsAt env e
          let some μ := env.refineComparable? [] (env.comparableArgs e argsE) | continue
          let ty := Ty.struct e (argsE.map (·.subst μ))
          let sd ← fresh ty
          let ctx' := { ctx with
            locals := { name := s!"$self{sd}", slot := sd, ty, mutable := false } ::
              ((locs ++ ctx.locals).map fun l => { l with ty := l.ty.subst μ }),
            types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst μ) } }
          let rc ← cb.elabApp ctx' p (.ident mp fname) (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
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
        let argsE := if env.isSub c e then mc.argsAt env e else env.argsBelow c targs e (extOf pins)
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
        let rc ← cb.elabDefaultDispatch ctx' p fname (.ident mp selfName :: argIds.toList) bracket
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
    let argsE := mc.argsAt env e
    let some μ := env.refineComparable? [] (env.comparableArgs e argsE) | continue
    let ty := Ty.struct e (argsE.map (·.subst μ))
    let sd ← fresh ty
    let ctx' := { ctx with
      locals := { name := s!"$self{sd}", slot := sd, ty, mutable := false } ::
        ((locs ++ ctx.locals).map fun l => { l with ty := l.ty.subst μ }),
      types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst μ) } }
    let rc ← cb.elabApp ctx' p (.ident mp fname) (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
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
    let body ← if ms.suspends then cb.withDeferMark ctx (.assign y acc) else pure (.assign y acc)
    return ⟨pre.toList.foldr Expr.seq body, msRet⟩
  return ⟨pre.toList.foldr Expr.seq acc, msRet⟩

/-- A call through a value of a class with value semantics: one test of the
    option of the receiver's tuple that is set, per class, then that
    class's implementation. -/
partial def elabValueDispatch (cb : AppElab) (ctx : Ctx) (p : Pos) (mc : MethodCall) (da : DispatchArgs) :
    EM R := do
  let env := ctx.types
  let mut acc : Expr := .prim .userErr []   -- no option set: unreachable
  for (d, j) in (mc.ds.zip (List.range mc.ds.length)).reverse do
    let some fname := ctx.implFor? d mc.root mc.m | eerr p s!"class {d} does not implement '{mc.m}'"
    let td ← fresh (classRepTy env d)
    let sd ← fresh (.struct d [])
    let ctx' := { ctx with locals := { name := s!"$self{sd}", slot := sd, ty := .struct d [], mutable := false } :: (da.locs ++ ctx.locals) }
    let rc ← cb.elabApp ctx' p (.ident mc.mp fname) (.ident mc.mp s!"$self{sd}" :: da.argIds.toList) mc.bracket mc.exp
    acc := .ite (.assign td (.prim .query [.prim (.tupGet j) [.local mc.slot]]))
      (.seq (.assign sd (classWrap env d d (.local td))) (← coerce p rc da.msRet)) acc
  let y ← fresh da.msRet
  return ⟨da.pre.toList.foldr Expr.seq (.assign y acc), da.msRet⟩

/-- `X.M(…)` of a method `M` that the class or interface `c` of `X` has
    (declared at `owner`): checked (access; the slots the call covers, #70:
    every class below `c` must implement them alike, or the call must say
    which; brackets; the number of arguments), the receiver evaluated
    first, then a direct call of the one implementation, or a dispatch on
    the class of the receiver's object, in which the arguments are
    evaluated once each before the implementation of that class is called:
    spawned, through views, through a reference or through a value. -/
partial def elabMethodCall (cb : AppElab) (ctx : Ctx) (p mp : Pos) (obj : SExpr) (r : R)
    (c : String) (targs : List Ty) (owner m : String) (spawning : Bool) (args : List SExpr)
    (bracket : Bool) (exp : Option Ty) : EM R := do
  let env := ctx.types
  -- (a field's accessor called for a use of the field: the field's access
  -- was judged there; the rest of the call is ordinary code)
  if !ctx.accessorCall then checkMemberAccess env p c m
  let ctx := { ctx with accessorCall := false }
  let roots := ctx.rootsOf c m
  let root := roots.headD owner
  for d in env.concreteBelow c do
    for o in roots do
      if ctx.implFor? d o m != ctx.implFor? d root m then
        eerr p s!"{d} implements {m} separately for {root} and {o}: call it as X.({root}:){m}(…) or X.({o}:){m}(…)"
  let ms := (ctx.sig? s!"{owner}.{m}").get!
  let args := packCallArgs p { ms with params := ms.params.drop 1, pnames := ms.pnames.drop 1 } args false
  if spawning && !ms.suspends then
    eerr p "spawn{…} takes a call of a <suspends> function (#156)"
  if ms.decides && !bracket then eerr p s!"{m} is <decides>: call it with {m}[…]"
  if !ms.decides && bracket then eerr p s!"{m} cannot fail: call it with {m}(…)"
  if ms.named.isEmpty && args.length + 1 != ms.params.length then
    eerr p s!"{m} takes {ms.params.length - 1} argument(s), found {args.length}"
  let slot ← fresh r.ty
  if !ctx.typeOnly then
    modify fun st => { st with metadataUses := slot :: st.metadataUses }
  let mc : MethodCall := { c, targs, m, owner, root, ms, recv := r, slot, obj,
                           ds := env.concreteBelow c, mp, spawning, args, bracket, exp }
  if let some fname := directImplementation? ctx mc then
    return ← elabDirectMethodCall cb ctx p mc fname
  let da ← dispatchArgs cb ctx p mc
  if spawning then return ← elabSpawnMethodDispatch cb ctx p mc da
  if env.viewed.contains c then return ← elabViewDispatch cb ctx p mc da
  if env.isRefClass c then return ← elabReferenceDispatch cb ctx p mc da
  elabValueDispatch cb ctx p mc da

/-- `X.M(…)`, `X.M[…]` (`f`, as written), the kinds of a call through a
    value, in the order they are tried: a type value is no receiver; the
    concurrency methods of a type parameter's value, of a task and of an
    event; then, of the receiver (bound, `elabBoundReceiverWith`, and
    qualified, `X.(i:)M`): an overloaded method's call, a method's call, a
    field's value indexed or called, and of a value of a built-in type, its
    built-in method (`elabMethod`). -/
partial def elabMemberApp (cb : AppElab) (ctx : Ctx) (p : Pos) (f : SExpr) (mp : Pos) (obj : SExpr)
    (m0 : String) (args : List SExpr) (bracket : Bool) (exp : Option Ty) : EM R := do
  if !ctx.typeOnly && ctx.isTypeValue obj then
    eerr mp "dummy type value cannot be an executable method receiver"
  let spawning := m0.startsWith "$spawnMethod:"
  let m0 := if spawning then (m0.drop 13).toString else m0
  if let some r ← elabParamConcurrencyCall? cb ctx p mp obj m0 spawning args bracket exp then return r
  if let some r ← elabTaskCancel? cb ctx p obj m0 args then return r
  if let some r ← elabEventSignal? cb ctx p mp obj m0 args bracket exp then return r
  if let some r ← elabAwait? cb ctx p mp obj m0 args exp then return r
  let r0 ← elabBoundReceiverWith cb.elabE ctx p (← cb.elabE ctx obj none) m0
  ctx.noteFamily mp r0.ty m0
  let (r, m) ← qualifiedReceiver ctx p r0 m0
  match r.ty with
  | .struct c targs =>
    if let some r' ← elabOverloadedMethodCall? cb ctx p mp obj c m m0 spawning args bracket exp then
      return r'
    -- (#283) a method overloaded in another hierarchy than `c`'s: the
    -- call takes `c`'s one list
    ctx.noteOverload p m m
    if let (true, some owner) := (ctx.types.classes.contains c, ctx.methodDecl? c m) then
      return ← elabMethodCall cb ctx p mp obj r c targs owner m spawning args bracket exp
    -- `S.F[i]`, `S.F(k)`: a field, indexed
    if (ctx.types.fields c targs).any (·.1 == m) then
      return ← elabValueApp cb ctx p f (← cb.elabMember ctx p r m none) args bracket
    if ctx.types.classes.contains c then eerr p s!"class {c} has no method '{m}'"
    eerr p s!"struct {c} has no field '{m}' (structs have no methods)"
  | _ => cb.elabMethod ctx p r m args bracket

/-! ## The kinds of application, in order -/

/-- `F(…)`, `F[…]`: an application, of the kind its callee `f` makes it,
    tried in this order (the order decides which meaning an application
    that could have two gets, and which refusal one that has none gets):

    1. `(t)(X)`, a conversion to a type written as one;
    2. of a name `F`:
       a. an extension method's call (`$ext:M(X, …)`);
       b. a local's: a cast through a type value, or its value indexed or
          called;
       c. in a method, `Self.F(…)`, of a method or a field of `Self`;
       d. a cast to a class or interface `F` (`elabCast`);
       e. a cast to a refinement type `F`;
       f. a conversion to a built-in type, struct or enum `F`;
       g. a call of an overloaded function;
       h. a call of a built-in function (`builtinFunctions`);
       i. a call of the program's function, or its constant's value indexed;
    3. `(super:)M(…)`;
    4. `X.M(…)`, through a value (`elabMemberApp`);
    5. any other value's application, indexed or called. -/
partial def elabAppBaseWith (cb : AppElab) (ctx : Ctx) (p : Pos) (f : SExpr) (args : List SExpr)
    (bracket : Bool) (exp : Option Ty) : EM R := do
  match f with
  | .construct _ "$type" [t] [] => elabWrittenConversion cb ctx p t args bracket
  | .ident fp name =>
    if let some r ← elabExtensionCallWith cb.elabE cb.elabApp ctx p fp name args bracket exp then return r
    if let some l := ctx.lookup name then return ← elabLocalApp cb ctx p f name l args bracket exp
    if callsSelfMember ctx name then
      return ← cb.elabApp ctx p (.member p (.ident p "Self") name) args bracket exp
    if ctx.types.classes.contains name && (ctx.sig? name).isNone then
      return ← cb.elabCast ctx p name args bracket
    if let some (base, conds) := ctx.types.refines.lookup name then
      return ← elabRefinementCast cb.elabE ctx p name base conds args bracket
    if convertsByName ctx name bracket then
      return ← elabConversionWith cb.elabE ctx p (.name name) args
    if let some ovs := ctx.types.overloads.lookup name then
      return ← elabOverloadedCall cb ctx p name ovs args bracket exp
    let (builtin, name) := builtinCalled ctx name
    if let some b := builtinFunctions.find? (·.name == builtin) then
      return ← b.elaborate { elabE := cb.elabE, elabArgs := cb.elabArgs, elabInts := cb.elabInts,
                             ctx, p, name, arity := b.arity, args, bracket, exp }
    elabFunctionCall cb ctx p f name args bracket exp
  | .member mp (.ident _ "(super:)") m => elabSuperCall cb ctx p mp m args bracket exp
  | .member mp obj m => elabMemberApp cb ctx p f mp obj m args bracket exp
  | _ => elabValueApp cb ctx p f (← cb.elabE ctx f none) args bracket

end OpenVerse.Front
