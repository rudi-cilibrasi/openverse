/- Elaboration of a program's type environment (phases 7–9 of `elabProgramCore`);
   public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Source
import OpenVerse.Front.Elab.Classes

namespace OpenVerse.Front
open OpenVerse

/-- The type environment, a phase of `elabProgramCore`: the classes' hierarchy
    (and the concrete classes below each), their var fields, `<unique>` ones,
    abstract methods and the classes that override or implement one, the home
    of each inherited default (#39); the enums, the structs with their fields'
    types resolved (classes' included), the refinement types (#136), the
    structs' type parameters, and the type arguments each class gives its
    parent class (#39) and the parametric interfaces it lists (#53), comparable
    where they must be; and the requests and the inlining's sites (`Source`). -/
def typeEnvironment (classes : Classes) (fields : Fields) (methods : Methods) (source : Source)
    (concurrencyNames : List (String × String)) (requests : Requests) (signalNoRollback : Bool) :
    Except String TyEnv := do
  let varFields : List (String × String) := classes.defs.flatMap fun cd =>
    (fields.of cd.name).filterMap fun (f, _, _, isVar) => if isVar then some (cd.name, f) else none
  let uniques : List String := (classes.defs.filter (·.specs.contains "unique")).map (·.name)
  let finalFields : List (String × String) := classes.defs.flatMap fun cd =>
    cd.fields.filterMap fun f => if f.specs.contains "final" then some (cd.name, f.name) else none
  let mut env : TyEnv := { constructionFx := source.constructionFx, access := source.access, concurrencyNames, finalFields, classes := classes.henv.classes, cinfo := classes.henv.cinfo, cinfoMap := classes.henv.cinfoMap,
                           classIx := classes.henv.classes.zipIdx.foldl (fun m (n, i) => m.insert n i) {},
                           belowReady := true,
                           supersMap := classes.henv.classes.foldl (fun m d => m.insert d (classes.henv.supers d)) {},
                           belowMap := classes.henv.classes.foldl (fun m d =>
                             let i := classes.henv.info d
                             if i.isIface || i.isAbstract then m else
                             (classes.henv.supers d).foldl (fun m T => m.insert T ((m[T]?.getD []) ++ [d])) m) {},
                           abstracts := methods.abstracts.toList, requests, signalNoRollback, familySites := source.familySites, familyStubs := methods.stubs.map (·.1),
                           overloadSites := source.overloadSites, nestedSites := source.nestedSites,
                           fieldSites := source.fieldSites }
  env := { env with varFields := varFields, uniques := uniques,
                    overriders := (methods.overridePairs.toList.map fun (_, dm, _) => (dm.splitOn ".").headD "") ++
                      (methods.implChecks.toList.map fun (_, _, impl, _) => (impl.splitOn ".").headD "") ++
                      -- (#250: and the targets of refining casts, whose own
                      -- pins relate their type arguments to the object's, as
                      -- the dispatch to the branch refines by: also one that
                      -- only inherits and gives its parent a compound of its
                      -- own, `c1(t) := class(c0([]t))`, #243, #351)
                      (requests.casts.map (·.target)) ++
                      (requests.loops.filterMap fun lift =>
                        if (lift.name.splitOn "$dispatchDefaultsSpawn").length > 1 then
                          some ((lift.name.splitOn ".").headD "") else none) }
  -- the class whose code each inherited field default is (#39): the nearest
  -- one, the class's own first, that gives the field a default itself
  let homeOf (c f : String) : String :=
    ((classes.henv.supers c).find? fun x =>
      ((classes.cdef? x).map fun xd => xd.fields.any fun g => g.name == f && g.default.isSome).getD false).getD c
  env := { env with defaultHome := classes.defs.flatMap fun cd =>
    (fields.of cd.name).filterMap fun (f, _, d, _) => d.map fun _ => ((cd.name, f), homeOf cd.name f) }
  for t in methods.tops do
    match t with
    | .const _ n _ none (.enumDef _ vals isOpen) =>
      env := { env with enums := env.enums ++ [(n, vals)],
                        openEnums := if isOpen then env.openEnums ++ [n] else env.openEnums }
    | .const _ n _ none (.structDef _ _ _ _) => env := { env with structs := env.structs ++ [(n, [])] }
    | .const p n _ none (.refineDef _ v sty conds) =>
      -- a refinement type (#136)
      let (base, _) ← (resolveTy env p sty).run {}
      env := { env with refines := env.refines ++ [(n, base, ← refineConds p v base conds)] }
    | _ => pure ()
  -- the type parameters of parametric structs
  for t in methods.tops do
    match t with
    | .const _ n _ none (.structDef _ tps@(_ :: _) _ _) =>
      env := { env with sparams := env.sparams ++ [(n, ← checkTParams env tps)] }
    | _ => pure ()
  let shell := env
  let mut structs := #[]
  for t in methods.tops do
    match t with
    | .const p n _ none (.structDef _ _ _ fs) =>
      let senv := { shell with tvars := (shell.sparams.lookup n).getD [] |>.map fun (v, c) => (v, Ty.param v c) }
      let fields ← fs.mapM fun ⟨f, sty, d, _, _, _⟩ => do
        let (ty, _) ← (resolveTy senv p sty).run {}
        pure (f, ty, d)
      structs := structs.push (n, fields)
    | _ => pure ()
  env := { env with structs := structs.toList }
  -- what `<persistable>` requires of a struct (Book of Verse ch. 17,
  -- `EffectPolicy.specifierPlaces`): no type parameters, and fields whose
  -- types persist, not `any`, `comparable` (ch. 17, 178: "Abstract interface
  -- type"), a rational, a function, an interface or a class
  -- (openverse has no persistable classes), nor a struct that is not
  -- `<persistable>`. (An enum's `<persistable>` the parser takes and drops:
  -- every enum is taken to persist.)
  let persistable : List String := methods.tops.filterMap fun
    | .const _ n _ none (.structDef _ _ specs _) => if specs.contains "persistable" then some n else none
    | _ => none
  let rec persists : Ty → Bool
    | .any | .dyn | .rational | .param .. => false
    | .arr t | .opt t => persists t
    | .tup ts => ts.attach.all fun ⟨t, _⟩ => persists t
    | .map k v => persists k && persists v
    | .struct n args => !env.classes.contains n && persistable.contains n && args.attach.all fun ⟨t, _⟩ => persists t
    | _ => true
  for t in methods.tops do
    if let .const p n _ none (.structDef _ tps specs _) := t then
      if specs.contains "persistable" then
        if !tps.isEmpty then throw s!"{p.show}: {n} is <persistable>, so it cannot have type parameters"
        for (f, ty, _) in (env.structs.lookup n).getD [] do
          if !persists ty then
            throw s!"{p.show}: {n} is <persistable>, so its field '{f}' must persist, and {ty.show} does not (Book of Verse ch. 17)"
  -- the type arguments of each class's parametric superclass (#39)
  let mut pargs : Array (String × List Ty) := #[]
  for cd in classes.defs do
    if let some q := (classes.henv.info cd.name).parent then
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
  for cd in classes.defs do
    for (q, qargs) in cd.parents.zip cd.parentArgs do
      if (classes.henv.info q).isIface && qargs.isEmpty && !((env.sparams.lookup cd.name).getD []).isEmpty then
        iargs := iargs.push ((cd.name, q), [])
      if (classes.henv.info q).isIface && !qargs.isEmpty then
        let cenv := { env with tvars := ((env.sparams.lookup cd.name).getD []).map fun (v, c) => (v, Ty.param v c) }
        let tys ← qargs.mapM fun sty => do
          let (ty, _) ← (resolveTy cenv cd.pos sty).run {}
          pure ty
        for (ty, (v, needComp)) in tys.zip ((env.sparams.lookup q).getD []) do
          if needComp && !ty.comparable env then
            throw s!"{cd.pos.show}: {cd.name} gives {q} the type argument {ty.show} for {v}, which must be comparable"
        iargs := iargs.push ((cd.name, q), tys)
  env := { env with iargs := iargs.toList }
  return env

/-- Upper bounds (#520), a phase of `elabProgramCore`: the bounds of the type
    parameters of the structs `tops` (classes' included) and the relations
    their fields declare, resolved for every constrained header before any use
    is checked, so that forward declarations do not depend on source order;
    then each bound, field type and parent's type arguments checked against
    them. -/
def upperBounds (env : TyEnv) (tops : List STop) : Except String TyEnv := do
  let mut env := env
  -- Resolve every constrained nominal header before validating any use of
  -- one. This makes forward declarations independent of source order.
  let constrainedTypes := tops.filterMap fun
    | .const p name _ none (.structDef _ tps _ fields) =>
      let relations := fields.filterMap fun f =>
        SubtypeEvidence.declaredRelation? name f.name f.ty f.isVar

      if tps.any (·.upperBound.isSome) || !relations.isEmpty then some (p, name, tps, relations) else none
    | _ => none
  if !constrainedTypes.isEmpty then
    let declarations ← constrainedTypes.mapM fun (p, name, tps, relations) => do
      let resolved ← resolveTParams { env with sbounds := [] } tps
      let scope := resolved.env { env with sbounds := [] }
      let extra ← relations.mapM fun (base, derived) => do
        let base ← (resolveTy scope p base).run' { env := scope }
        let derived ← (resolveTy scope p derived).run' { env := scope }
        pure (SubtypeEvidence.Bound.mk base derived)
      pure (p, name, { resolved with bounds := resolved.bounds ++ extra })
    env := { env with sbounds := declarations.map fun (_, name, resolved) =>
      (name, resolved.bounds.map fun bound => (bound.base, bound.derived)) }
    for (p, _, resolved) in declarations do
      let scope := resolved.env env
      for bound in resolved.bounds do
        for ty in [bound.base, bound.derived] do
          match ty.checkBounds scope with
          | .error message => throw s!"{p.show}: {message}"
          | .ok _ => pure ()
    for (name, fields) in env.structs do
      let scope := { env with
        tvars := ((env.sparams.lookup name).getD []).map fun (v, c) => (v, Ty.param v c)
        boundFacts := (env.sbounds.lookup name).getD [] ++ SubtypeEvidence.fieldFacts env name fields }
      for (field, ty, _) in fields do
        match ty.checkBounds scope with
        | .error message => throw s!"field '{field}' of {name}: {message}"
        | .ok _ => pure ()
      for (owner, args) in ((env.pargs.lookup name).toList.map fun args =>
          ((env.info name).parent.getD "", args)) ++
          (env.iargs.filterMap fun ((source, target), args) =>
            if source == name then some (target, args) else none) do
        -- An omitted generic interface prefix is resolved by the existing
        -- interface-layout checks; explicit arguments are checked here.
        if !args.isEmpty then
          match (Ty.struct owner args).checkBounds scope with
          | .error message => throw s!"parent {owner} of {name}: {message}"
          | .ok _ => pure ()
  return env

/-- The interfaces referred to through views (`interfaceViews`). -/
structure Views where
  /-- The interfaces whose Verse Core type arguments at a class below them are
      not a prefix of the class's, referred to through views (#351), and the
      interfaces above them (`TyEnv.viewed`). -/
  viewed : List String
  /-- The classes whose hidden fields must hold all their type parameters for
      that, which they do not yet: the next elaboration gives them those
      (`Requests.witnesses`). -/
  witnessNeeds : List String

/-- Views (#351), a phase of `elabProgramCore`: a class implements one instance
    of each interface above it (#53); an interface whose Verse Core type
    arguments at a class below it are not a prefix of the class's is referred
    to through views, and the classes below it, and those whose default
    bridges or spawn adapters open type parameters (`requests.loops`), need
    hidden fields for all of their type parameters. -/
def interfaceViews (env : TyEnv) (cdefs : List CDef) (requests : Requests) : Except String Views := do
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
          -- (#351) references to the interface go through views, each class
          -- below with its own; its fields would be at other places in its
          -- classes, which no view gives
          -- (a dispatch through a view reads all of the class's type
          -- arguments from its hidden fields, which a class without a class
          -- parent has for all of them; one with one, which adds the
          -- interface, has them for all only when asked, and the program is
          -- elaborated again, `Requests.witnesses`)
          if let some q := (env.info cd.name).parent then
            if !env.isSub q i && !requests.witnesses.contains cd.name && !witnessNeeds.contains cd.name then
              witnessNeeds := witnessNeeds ++ [cd.name]
          viewed := viewed ++ [i]
  for lift in requests.loops do
    if defaultBridge lift.name || spawnAdapter lift.name then
      let cls := (lift.name.splitOn ".").headD ""
      let needed := lift.specs.filterMap fun flag =>
        if flag.startsWith "$selfTp:" then some (flag.drop 8).toString else none
      if needed.any (fun n => (env.witnessField? cls n).isNone) &&
          !requests.witnesses.contains cls && !witnessNeeds.contains cls then
        witnessNeeds := witnessNeeds ++ [cls]
  -- (and the interfaces above them, which see their classes through a
  -- prefix of what they do)
  return { viewed := (viewed ++ viewed.flatMap fun i => (env.supers i).filter (env.info · |>.isIface)).eraseDups,
           witnessNeeds }

/-- Pins and accessors, a phase of `elabProgramCore`: an override's class has
    the Verse Core type arguments of the class it overrides in, but for those
    it fixes or relates (not through views, #351); the classes whose
    implementations fix type arguments their declaring class leaves open, and
    the classes below them, record their pins (#142); and the fields read
    through accessors (#157, #205, #351). -/
def pinsAndAccessors (env : TyEnv) (methods : Methods) (requests : Requests) : Except String TyEnv := do
  let mut env := env
  for (mp, dm, qm) in methods.overridePairs do
    let d := (dm.splitOn ".").head!
    let q := (qm.splitOn ".").head!
    let mn := (dm.splitOn ".").getLast!
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
  let pinClasses := (methods.overridePairs.toList.flatMap fun (_, dm, qm) =>
      [(dm.splitOn ".").head!, (qm.splitOn ".").head!]).eraseDups
  env := { env with pinsMap := pinClasses.foldl (fun m d => m.insert d (env.pinsOf d)) {} }
  let fixes (e q : String) : Bool :=
    ((env.pinsOf q).zip (env.pinsOf e)).any (fun (a, b) => a != b) || (env.pinsOf e).length > (env.pinsOf q).length
  let headOf (f : String) : String := (f.splitOn ".").head!
  let fixers := (methods.overridePairs.toList.filterMap fun (_, dm, qm) =>
      if fixes (headOf dm) (headOf qm) then some (headOf dm) else none) ++
    (methods.implChecks.toList.filterMap fun (_, _, impl, decl) =>
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
  let spawnFixers := requests.loops.filterMap fun lift =>
    if (lift.name.splitOn "$dispatchDefaultsSpawn").length > 1 then
      some ((lift.name.splitOn ".").headD "") else none
  let fixers := fixers ++ accFixers.toList ++ env.requests.casts.map (·.target) ++ spawnFixers
  env := { env with pinned := env.classes.filter fun d => fixers.any fun f => d == f || (env.supers d).contains f,
                    fieldAcc := fieldAcc.toList }
  return env

/-- Placeholders and prototypes, a phase of `elabProgramCore`: a hidden class
    below each generic class or interface whose concrete classes all fix some
    of its type arguments (#157), the prototypes (#37); and no struct, and no
    class's Verse Core type, contains itself (#63), and every map key in a
    field's type is comparable. -/
def addPlaceholders (env : TyEnv) : Except String TyEnv := do
  let mut env := env
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
  return env

end OpenVerse.Front
