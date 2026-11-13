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
    (concurrencyNames : List (String × String)) (requests : Requests) : Except String TyEnv := do
  let varFields : List (String × String) := classes.defs.flatMap fun cd =>
    (fields.of cd.name).filterMap fun (f, _, _, isVar) => if isVar then some (cd.name, f) else none
  let uniques : List String := (classes.defs.filter (·.specs.contains "unique")).map (·.name)
  let mut env : TyEnv := { constructionFx := source.constructionFx, concurrencyNames, classes := classes.henv.classes, cinfo := classes.henv.cinfo, cinfoMap := classes.henv.cinfoMap,
                           classIx := classes.henv.classes.zipIdx.foldl (fun m (n, i) => m.insert n i) {},
                           belowReady := true,
                           supersMap := classes.henv.classes.foldl (fun m d => m.insert d (classes.henv.supers d)) {},
                           belowMap := classes.henv.classes.foldl (fun m d =>
                             let i := classes.henv.info d
                             if i.isIface || i.isAbstract then m else
                             (classes.henv.supers d).foldl (fun m T => m.insert T ((m[T]?.getD []) ++ [d])) m) {},
                           abstracts := methods.abstracts.toList, requests, familySites := source.familySites, familyStubs := methods.stubs.map (·.1),
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
      ((classes.cdef? x).map fun xd => xd.fields.any fun (g, _, d, _) => g == f && d.isSome).getD false).getD c
  env := { env with defaultHome := classes.defs.flatMap fun cd =>
    (fields.of cd.name).filterMap fun (f, _, d, _) => d.map fun _ => ((cd.name, f), homeOf cd.name f) }
  for t in methods.tops do
    match t with
    | .const _ n none (.enumDef _ vals isOpen) =>
      env := { env with enums := env.enums ++ [(n, vals)],
                        openEnums := if isOpen then env.openEnums ++ [n] else env.openEnums }
    | .const _ n none (.structDef _ _ _ _) => env := { env with structs := env.structs ++ [(n, [])] }
    | .const p n none (.refineDef _ v sty conds) =>
      -- a refinement type (#136)
      let (base, _) ← (resolveTy env p sty).run {}
      env := { env with refines := env.refines ++ [(n, base, ← refineConds p v base conds)] }
    | _ => pure ()
  -- the type parameters of parametric structs
  for t in methods.tops do
    match t with
    | .const _ n none (.structDef _ tps@(_ :: _) _ _) =>
      env := { env with sparams := env.sparams ++ [(n, ← checkTParams env tps)] }
    | _ => pure ()
  let shell := env
  let mut structs := #[]
  for t in methods.tops do
    match t with
    | .const p n none (.structDef _ _ _ fs) =>
      let senv := { shell with tvars := (shell.sparams.lookup n).getD [] |>.map fun (v, c) => (v, Ty.param v c) }
      let fields ← fs.mapM fun (f, sty, d, _) => do
        let (ty, _) ← (resolveTy senv p sty).run {}
        pure (f, ty, d)
      structs := structs.push (n, fields)
    | _ => pure ()
  env := { env with structs := structs.toList }
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
    | .const p name none (.structDef _ tps _ fields) =>
      let relations := fields.filterMap fun (field, ty, _, mutable) =>
        SubtypeEvidence.declaredRelation? name field ty mutable
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

end OpenVerse.Front
