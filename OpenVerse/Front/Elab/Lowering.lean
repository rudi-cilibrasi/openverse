/- Elaboration lowering; public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Expr

namespace OpenVerse.Front
open OpenVerse
/-- An elaborated program and the certificate under which it type-checks:
    `prog.check`, `prog.checkTypes sigs slotTys` and `prog.checkControl` hold,
    so `Prog.accepted` applies to it. Unless the elaboration asks for
    something (`needs`): it then went no further, and the program is to be
    elaborated again with it (`Compiled.asking`). -/
structure Compiled where
  prog    : Prog
  sigs    : Sigs
  slotTys : List (List VTy)
  needs : Requests := {}

/-- An elaboration that goes no further, as the program is to be elaborated
    again with `needs`. -/
def Compiled.asking (needs : Requests) : Compiled :=
  { prog := default, sigs := { fns := [] }, slotTys := [], needs }

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
    expression to run instead of `Main`; and what earlier elaborations of it
    asked for (`requests`, which `elabProgram` gives). -/
structure Options where
  profile : SourceProfile := .full
  /-- Explicit compatibility mode for OpenVerse's extended field defaults.
      It retains heap/failure checks, without asserting initializer convergence. -/
  extendedDefaults : Bool := false
  args : Option (List String) := none
  entry : Option SExpr := none
  /-- On an internal error (an elaborated function the checker rejects),
      also print that function's Verse Core, its slot types and signature,
      for a bug report (`OPENVERSE_DEBUG=1`). -/
  debug : Bool := false
  /-- (#513) Resume the tasks an event's `Signal` wakes in the order they
      began to wait (FIFO), the published API's order, instead of the
      scheduler's (`Main`, then the roots in spawn order): opt-in, so that
      existing traces keep theirs until a default is chosen. -/
  eventFifo : Bool := false
  requests : Requests := {}

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
      out := out.push (.const p fieldsTy none (.structDef p sparams [] (fs.map fun f => (f, tyOf f, none, false))))
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

/-- The class of the cells of the stack a lazily taken function with
    several values runs its calls from (#246): an item, and the cells
    below it. Added to a program that has such a function. -/
def lazyPrelude : String := "
lazycell(t:type) := class:
    LItem:t
    LNext:?lazycell(t)
"

def lazyTops : Except String (List STop) := parsePrelude lazyPrelude ["lazycell", "LItem", "LNext"]

/-- (#283) A `var` of a lazily taken recursive function that a return frame
    sets, as a cell (`Choice.cellVars`). -/
def varcellPrelude : String := "
varcell(t:type) := class:
    var VCell:t
"

def varcellTops : Except String (List STop) := parsePrelude varcellPrelude ["varcell", "VCell"]

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

def subTops (owned : List String := []) : Except String (List STop) :=
  parsePrelude subPrelude (owned ++ ["subscription", "Live", "Handlers", "Hs", "H", "S", "F", "X", "t", "Head", "signalAll"])

def subVoidTops (owned : List String := []) : Except String (List STop) :=
  parsePrelude subVoidPrelude (owned ++ ["subscription", "Live", "Handlers", "Hs", "H", "S", "F", "X", "Head", "signalAll", "subev0"])

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
def functionBodyCtx (req : Requests) (ctx : Ctx) (p : Pos) (name : String)
    (tps : List (String × Bool)) (scopeClass : Option String := none) : Except String Ctx := do
  let lifted := req.casts.find? (·.name == name)
  let loopLift := if name.startsWith "$choiceOperationDictionary" then none else
    req.loops.find? fun l => l.name == name || l.extraFns.any
      (fun | .fn _ n .. => n == name | _ => false)
  let resume := req.loops.findSome? fun l => l.resumes.find? (·.name == name)
  let source := (resume.map (·.sourceContext)).getD
    ((loopLift.map (·.sourceContext)).getD ((lifted.map (·.sourceContext)).getD {}))
  let returnExit := loopLift.bind (·.returnExit)
  let breakExit := loopLift.bind (·.breakExit)
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
    refineExits := if returnExit.isNone && breakExit.isNone then (lifted.map (·.exits)).getD {} else
      { ret := returnExit.map fun r => (r.value.map (fun n => (n, r.ty)), r.packet), brk := breakExit }
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
    (forced : List Nat := []) (frameInfo : Array FrameRefs.Info := #[]) (fifo : Bool := false) :
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
        (.heap (.set (fieldIdx (env.concurrencyName "task") "$Result")) [.local 0, .prim .mkSome [.call h ((List.range n).map (fun i => Expr.local (i + 1)))]])
        (.seq (.heap (.set (fieldIdx (env.concurrencyName "task") "$Done")) [.local 0, .lit (.logic true)]) (.lit .void))
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
  let lifts := lows.filter fun (_, name, _) => defaultBridge name || choiceDefaultBridge name || env.castRequests.any (·.name == name)
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
  let tDoneF := fieldIdx (env.concurrencyName "task") "$Done"
  let tCancelledF := fieldIdx (env.concurrencyName "task") "$Cancelled"
  let runningF := fieldIdx (env.concurrencyName "task") "$Running"
  let rootF := fieldIdx (env.concurrencyName "task") "$Root"
  let cancelReqF := fieldIdx (env.concurrencyName "task") "$CancelReq"
  -- (#260: the task whose code runs, a dummy one for `Main`'s; a branch's
  -- wrapper records it as its owner, which is running while the branch
  -- runs)
  let curTaskF := fieldIdx "$sched" "$CurTask"
  -- (#513, FIFO event resumption: the root running, the waiters `Signal`
  -- woke, in its order, and the root each waiter waits in)
  let curRootF := fieldIdx "$sched" "$CurRoot"
  let wokenHeadF := fieldIdx "$sched" "$WokenHead"
  let wokenTailF := fieldIdx "$sched" "$WokenTail"
  let waitRootF := fieldIdx "$taskBase" "$WaitRoot"
  let wokenNextF := fieldIdx "$taskBase" "$WokenNext"
  let pendingF := fieldIdx "$taskBase" "$Pending"
  let probeF := fieldIdx "$sched" "$Probe"
  let waitfTF := fieldIdx "$waitf" "$T"
  -- (`CurRoot := some x` and back, around a run, in FIFO mode)
  let setCur (sch x : Expr) : Expr := .heap (.set curRootF) [sch, .prim .mkSome [x]]
  -- (a waiter records the root it waits in when it is polled, after its
  -- slots' initialisations)
  if fifo then
    let wi := idxOf "$waitResume"
    if let some fn := fns[wi]? then
      if let some (ds, b) := Suspend.stripInits (fn.nslots - fn.arity) fn.body then
        let rec' : Expr := .heap (.set waitRootF) [.heap (.get waitfTF) [.local 0], .heap (.get curRootF) [.local 1]]
        fns := fns.set! wi { fn with body := (initPrefixE fn.arity ds (.seq rec' b)) }
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
      -- (#513: and, in FIFO mode, probes it as its own root, so that the
      -- waiters in it record that root, not the function's, which no
      -- longer runs it: a `Signal` before its first turn then gives it its
      -- turn in their order; the probe goes on nowhere, `$Probe`)
      let probe : List Expr := if !fifo then [] else [
        .assign 5 (.heap (.get curRootF) [.local 0]),
        .heap (.set probeF) [.local 0, .lit (.logic true)],
        setCur (.local 0) (.local 2),
        .assign 3 (.call (wrapFnBase + 3 * K) [.local 2, .local 0]),
        .heap (.set curRootF) [.local 0, .local 5],
        .heap (.set probeF) [.local 0, .lit (.logic false)]] ++ forget (.local 0)
      let start : Expr := .seq (Suspend.seqVoid (if !runNow then register :: probe else [register,
        .assign 4 (.heap (.get cancelCurF) [.local 0]),
        .heap (.set cancelCurF) [.local 0, .lit (.logic false)]] ++
        -- (#513: its run is the branch's, for the waiters it records)
        (if fifo then [.assign 5 (.heap (.get curRootF) [.local 0]), setCur (.local 0) (.local 2)] else []) ++
        -- (what its run recorded is forgotten, as after a root's, #362)
        [.assign 3 (.call (wrapFnBase + 3 * K) [.local 2, .local 0])] ++
        (if fifo then [.heap (.set curRootF) [.local 0, .local 5]] else []) ++ forget (.local 0) ++ [
        takeCancel (.local 2) (.local 3),
        .heap (.set cancelCurF) [.local 0, .local 4],
        .ite (.prim .eq [.local 3, Suspend.int 1])
          (.seq (Suspend.seqVoid [.heap (.set Suspend.pcF) [.local 2, Suspend.int (-1)],
            .heap (.set progressF) [.local 0, .lit (.logic true)], .heap (.set deadF) [.local 0, .lit (.logic true)]])
            Suspend.vd) Suspend.vd])) (.local 2)
      let startFn : Fn := { name := s!"$branch{K}$start", arity := 2, nslots := if fifo then 6 else 5, decides := false,
                            writes := true,
                            body := initPrefixE 2 ([.heap (.new (wrapTag K)) [Suspend.int 0, .local 1,
                              .heap (.get curTaskF) [.local 0]], Suspend.int 0,
                              .lit (.logic false)] ++ (if fifo then [.lit .none] else [])) start }
      branchFns := branchFns.push startFn
      branchTys := branchTys.push ([schedTy, frameTy j, wrapTy K, .int, .logic] ++ (if fifo then [.opt rootAny] else []))
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
      -- (#513: its first run is the new root's, for the waiters it records)
      (if fifo then [.assign 4 (.heap (.get curRootF) [.local 0]), setCur (.local 0) (.local 1)] else []) ++
      [.assign 2 (.call (trampOf k) [.local 1, .local 0])] ++
      (if fifo then [.heap (.set curRootF) [.local 0, .local 4]] else []) ++ forget (.local 0) ++ [
      takeCancel (.local 1) (.local 2),
      .heap (.set cancelCurF) [.local 0, .local 3],
      .ite (.prim .eq [.local 2, Suspend.int 1])
        (.seq (Suspend.seqVoid [.heap (.set Suspend.pcF) [.local 1, Suspend.int (-1)],
          .heap (.set progressF) [.local 0, .lit (.logic true)], .heap (.set deadF) [.local 0, .lit (.logic true)]])
          Suspend.vd) Suspend.vd])
    rootFns := rootFns.push { name := s!"$spawn{k}$start", arity := 2, nslots := if fifo then 5 else 4, decides := false,
                              writes := true,
                              body := initPrefixE 2 ([Suspend.int 0, .lit (.logic false)] ++
                                (if fifo then [.lit .none] else [])) start }
    rootTys := rootTys.push ([schedTy, frameTy j, .int, .logic] ++ (if fifo then [.opt rootAny] else []))
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
  -- (#513: the root fields hold roots, in the scheduler and every task)
  if fifo then
    classTable := classTable.set schedTag ((classTable[schedTag]!).set curRootF (.opt rootAny))
    for d in env.classes do
      if let some k := (env.fields d).findIdx? (·.1 == "$WaitRoot") then
        let t := env.tagOf d
        classTable := classTable.set t ((classTable[t]!).set k (.opt rootAny))
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
    -- (#513, FIFO: slots for the woken waiter and its root)
    let wv := if leafy then 10 else 8
    let ev := wv + 1
    -- (a root in slot `r`, not done: run, as `pollRoots` does)
    let runRoot : Expr :=
        .ite (.prim .ne [.heap (.get Suspend.pcF) [.local r], Suspend.int (-1)])
          (.seq (Suspend.seqVoid ((if fifo then [setCur sch (.local r)] else []) ++ [.assign st dispatch,
            .ite (.prim .query [.heap (.get cancelCurF) [sch]])
              (.seq (Suspend.seqVoid [.heap (.set cancelCurF) [sch, .lit (.logic false)],
                .ite (.prim .eq [.local st, Suspend.int 1]) Suspend.vd
                  (.seq (.call cancelRootIdx [sch, .local r]) Suspend.vd)]) Suspend.vd) Suspend.vd,
            .ite (.prim .eq [.local st, Suspend.int 1])
              (.seq (Suspend.seqVoid [.heap (.set Suspend.pcF) [.local r, Suspend.int (-1)],
                .heap (.set progressF) [sch, .lit (.logic true)], .heap (.set deadF) [sch, .lit (.logic true)]]) Suspend.vd)
              Suspend.vd])) Suspend.vd) Suspend.vd
    -- (`Main`, not done, run from the drain)
    let runMain : Expr := .ite (.prim .eq [.local mainDone, Suspend.int 1]) Suspend.vd
      (Suspend.seqVoid ([setCur sch (.local 1)] ++
        resumeChain (.local 1) sch (.call mainSig.idx [.local 1, sch]) topIdx[j]! st 8 9 ++ [
        .ite (.prim .eq [.local st, Suspend.int 1]) (.seq (.assign mainDone (Suspend.int 1)) Suspend.vd) Suspend.vd,
        .ite (.prim .query [.heap (.get cancelCurF) [sch]])
          (.seq (Suspend.seqVoid [.heap (.set cancelCurF) [sch, .lit (.logic false)],
            .call (nFns + 4 * j + 2) [.local 1, sch], .assign mainDone (Suspend.int 1)]) Suspend.vd) Suspend.vd]))
    -- (#513, FIFO: the waiters `Signal` woke, in its order, each one's root
    -- run now, before the scheduler's own order goes on; those they wake
    -- after them, in the same loop)
    let drain : List Expr := if !fifo then [] else [
      .loop (Suspend.seqVoid [
        -- (none once `Main` ended: the program ends with it)
        .ite (.prim .eq [.local mainDone, Suspend.int 1]) .brk Suspend.vd,
        .ite (.assign wv (.prim .query [.heap (.get wokenHeadF) [sch]])) Suspend.vd .brk,
        .heap (.set wokenHeadF) [sch, .heap (.get wokenNextF) [.local wv]],
        -- (its turn: it may go on now, and only it of its task's woken ones)
        .heap (.set pendingF) [.local wv, .lit (.logic false)],
        .ite (.prim .query [.heap (.get wokenHeadF) [sch]]) Suspend.vd
          (.seq (.heap (.set wokenTailF) [sch, .lit .none]) Suspend.vd),
        .ite (.assign ev (.prim .query [.heap (.get waitRootF) [.local wv]]))
          (.ite (.heap (.isTag [tagBase + mainJ]) [.local ev]) runMain
            (if rootTags.isEmpty then Suspend.vd else .seq (.assign r (.local ev)) runRoot))
          Suspend.vd])]
    let pollRoots : List Expr := if rootTags.isEmpty then [] else [
      .assign cur (.heap (.get headF) [sch]),
      .loop (Suspend.seqVoid ([
        .ite (.assign c (.prim .query [.local cur])) Suspend.vd .brk,
        .assign r (rootOf (.local c))] ++ (if fifo then [runRoot] ++ drain ++ [
          .ite (.prim .eq [.local mainDone, Suspend.int 1]) .brk Suspend.vd] else [
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
              Suspend.vd]) Suspend.vd) Suspend.vd]) ++ [
        .assign cur (.heap (.get nextF) [.local c])]))]
    let pass : Expr := .loop (Suspend.seqVoid ([
      .heap (.set progressF) [sch, .lit (.logic false)],
      .heap (.set 1) [sch, Suspend.int (-1)],
      ] ++ (if fifo then [setCur sch (.local 1)] else []) ++
      resumeChain (.local 1) sch (.call mainSig.idx [.local 1, sch]) topIdx[j]! st 8 9 ++ [
      .ite (.prim .eq [.local st, Suspend.int 1]) (.seq (.assign mainDone (Suspend.int 1)) .brk) Suspend.vd,
      -- (`Main` awaited a cancelled task: it is cancelled, and so the program ends)
      .ite (.prim .query [.heap (.get cancelCurF) [sch]])
        (.seq (Suspend.seqVoid [.heap (.set cancelCurF) [sch, .lit (.logic false)],
          .call (nFns + 4 * j + 2) [.local 1, sch], .assign mainDone (Suspend.int 1)]) .brk) Suspend.vd] ++
      drain ++ (if fifo then [.ite (.prim .eq [.local mainDone, Suspend.int 1]) .brk Suspend.vd] else []) ++
      pollRoots ++
      -- (FIFO: `Main` may end in a drain during the roots' poll)
      (if fifo then [.ite (.prim .eq [.local mainDone, Suspend.int 1]) .brk Suspend.vd] else []) ++
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
    fns := fns.push { name := "$Run", arity := 2, nslots := (if leafy then 10 else 8) + (if fifo then 2 else 0),
                      decides := false, writes := true,
                      body := initPrefixE 2 ([Suspend.int 0, Suspend.int 0, .local 1, .lit .none,
                        cellInit, cellInit] ++ (if leafy then [Suspend.int 0, Suspend.int 0] else []) ++
                        (if fifo then [.heap (.get curTaskF) [.local 0], .local 1] else [])) run }
    slotTys := slotTys.push ([schedTy, frameTy j, .int, .int, rootAny, .opt cellTy, cellTy, cellTy] ++
      (if leafy then [.int, .int] else []) ++ (if fifo then [taskBaseTy, rootAny] else []))
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
def checkEager (fns : Array Fn) (errs : Array (Option Pos)) (posOf : String → Option Pos)
    (lazy : List String := []) : Except String (List String) := do
  let mut needs : List String := []
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
        -- (#283) taken lazily instead, if its shape allows, after another
        -- elaboration; refused if it still is not
        if !lazy.contains g then
          needs := needs ++ [g]
          break
        throw s!"{loc}{g} has several values and is recursive, or called by a recursive one, and it may {what}{via}: {Choice.eagerWhy}"
      for (f, _) in Suspend.callsOf fj.body do
        if f < fns.size && !seen[f]! then
          seen := seen.set! f true
          todo := todo ++ [f]
  return needs

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

end OpenVerse.Front
