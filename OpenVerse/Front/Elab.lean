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
import OpenVerse.Front.Elab.Source
import OpenVerse.Front.Elab.Functions
import OpenVerse.Front.SignalAdmission
import OpenVerse.Front.InitializerConvergence

namespace OpenVerse.Front
open OpenVerse
/-- A program as the lowering leaves it (`lowerProgram`), before `certify`:
    its Verse Core functions, their signatures with the class table, the
    prototypes and the classes' pins (`Sigs`), and each function's slot types. -/
structure LoweredProgram where
  prog : Prog
  sigs : Sigs
  slotTys : Array (List VTy)

/-- Certification, the last phase of `elabProgramCore`: the lowered program is
    given out with its certificate (`Compiled`) only if no call in it names a
    family's stub (#283), and it passes `Prog.check`, `Prog.checkControl` and
    `Prog.checkTypes` under its signatures and slot types. A program that does
    not is an elaborator bug, refused as an internal error that names what
    fails (with `debug`, the function's Verse Core too, for a bug report). -/
def certify (lowered : LoweredProgram) (stubs : List (String × Pos)) (debug : Bool) :
    Except String Compiled := do
  let P := lowered.prog
  let S := lowered.sigs
  let slotTys := lowered.slotTys
  -- (#283) no call names a family's stub (`Choice.familyStub`), whose body
  -- is `Err()`: each call of a method of the family was rewritten not to be
  -- one, and a stub has no value (`FnValues`). Verse Core has no calls but
  -- those naming their function (dispatch is a test of the class, then a
  -- call), so whatever code made them, no stub runs
  for fn in P.fns do
    for (g, _) in Suspend.callsOf fn.body do
      if let some q := (P.fns[g]?).bind fun callee => stubs.lookup callee.name then
        throw s!"{q.show}: {Choice.shownFnName P.fns[g]!.name} has several values, but a call of it in {Choice.shownFnName fn.name} is compiled as one of a method of one value, where its receiver's class was not known: not supported yet (#283)"
  if !P.check then
    let bad := P.fns.filter fun fn => (!fn.decides && fn.body.mayFail P) ||
      (!fn.writes && fn.body.writesHeap P) || !(fn.body.scoped P fn.nslots)
    throw s!"internal error: the elaborated program does not pass Prog.check ({bad.map (·.name)})"
  if !P.checkControl then throw "internal error: the elaborated program does not pass Prog.checkControl"
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
        let dump := if !debug then "" else
          badStmt ++ s!"\n-- body:\n{((P.fns[f]?).map (fun (fn : Fn) => fn.body.compact "   ")).getD "?"}\n-- arity: {(P.fns[f]?).map Fn.arity}" ++
          s!"\n-- slot types: {repr (slotTys[f]?)}\n-- signature: {repr (S.fns[f]?)}"
        s!" (in {((P.fns[f]?).map Fn.name).getD "?"}){dump}"
      | none => if !checkPrelude P S then " (the prototypes)" else ""
    throw s!"internal error: the elaborated program does not pass Prog.checkTypes{which}"
  return { prog := P, sigs := S, slotTys := slotTys.toList }

/-- Elaborate a parsed program into a Verse Core program that passes `Prog.check`
    and `Prog.checkTypes`. -/
def elabProgramCore (allTops0r : List STop) (opts : Options := {}) : Except String Compiled := do
  let admitted ← admitSource allTops0r opts
  let source ← inlineSource allTops0r opts.requests admitted
  let defs ← argsAndMethodOverloads source.tops source.entry opts.args
  let classes ← classHierarchy defs.tops source.constructionFx
  let fields ← classFields classes opts.requests
  let methods ← classMethods defs.tops classes fields
  -- the type definitions: `name := struct …` and `name := enum …`
  let isTypeDef : STop → Bool
    | .const _ _ none (.structDef ..) | .const _ _ none (.enumDef ..) | .const _ _ none (.refineDef ..) => true
    | _ => false
  let tops := methods.tops.filter (!isTypeDef ·)
  let varFields : List (String × String) := classes.defs.flatMap fun cd =>
    (fields.of cd.name).filterMap fun (f, _, _, isVar) => if isVar then some (cd.name, f) else none
  let uniques : List String := (classes.defs.filter (·.specs.contains "unique")).map (·.name)
  let mut env : TyEnv := { constructionFx := source.constructionFx, concurrencyNames := admitted.concurrencyNames, classes := classes.henv.classes, cinfo := classes.henv.cinfo, cinfoMap := classes.henv.cinfoMap,
                           classIx := classes.henv.classes.zipIdx.foldl (fun m (n, i) => m.insert n i) {},
                           belowReady := true,
                           supersMap := classes.henv.classes.foldl (fun m d => m.insert d (classes.henv.supers d)) {},
                           belowMap := classes.henv.classes.foldl (fun m d =>
                             let i := classes.henv.info d
                             if i.isIface || i.isAbstract then m else
                             (classes.henv.supers d).foldl (fun m T => m.insert T ((m[T]?.getD []) ++ [d])) m) {},
                           abstracts := methods.abstracts.toList, requests := opts.requests, familySites := source.familySites, familyStubs := methods.stubs.map (·.1),
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
                      (opts.requests.casts.map (·.target)) ++
                      (opts.requests.loops.filterMap fun lift =>
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
  -- Resolve every constrained nominal header before validating any use of
  -- one. This makes forward declarations independent of source order.
  let constrainedTypes := methods.tops.filterMap fun
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
  for cd in classes.defs do
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
            if !env.isSub q i && !opts.requests.witnesses.contains cd.name && !witnessNeeds.contains cd.name then
              witnessNeeds := witnessNeeds ++ [cd.name]
          viewed := viewed ++ [i]
  for lift in opts.requests.loops do
    if defaultBridge lift.name || spawnAdapter lift.name then
      let cls := (lift.name.splitOn ".").headD ""
      let needed := lift.specs.filterMap fun flag =>
        if flag.startsWith "$selfTp:" then some (flag.drop 8).toString else none
      if needed.any (fun n => (env.witnessField? cls n).isNone) &&
          !opts.requests.witnesses.contains cls && !witnessNeeds.contains cls then
        witnessNeeds := witnessNeeds ++ [cls]
  if !witnessNeeds.isEmpty then
    return .asking { witnesses := witnessNeeds }
  -- (and the interfaces above them, which see their classes through a
  -- prefix of what they do)
  env := { env with viewed := (viewed ++ viewed.flatMap fun i => (env.supers i).filter (env.info · |>.isIface)).eraseDups }
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
  let spawnFixers := opts.requests.loops.filterMap fun lift =>
    if (lift.name.splitOn "$dispatchDefaultsSpawn").length > 1 then
      some ((lift.name.splitOn ".").headD "") else none
  let fixers := fixers ++ accFixers.toList ++ env.requests.casts.map (·.target) ++ spawnFixers
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
                      let bases := (defs.methodOverloads.lists.map (·.1.2)).eraseDups
                      bases.map fun mn =>
                        let n := (defs.methodOverloads.lists.filter (·.1.2 == mn)).foldl (fun acc (_, sigs) => max acc sigs.length) 0
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
  let inferredBridge (n : String) := defaultBridge n || opts.requests.casts.any (·.name == n)
  -- a function's parameter and result types
  let fnTypes (env : TyEnv) (p : Pos) (n : String) (ps : List SParam) (effs : List String) (ret : STy) :
      Except String (List Ty × Ty) := do
    if effs.contains "suspends" then
      if effs.contains "decides" then
        throw s!"{p.show}: {n} is both <suspends> and <decides>, which exclude each other"
      if n.endsWith "$init" then
        throw s!"{p.show}: a <suspends> constructor is not supported (#156)"
    let (tys, rt) ← resolveSignatureTypes env p ps ret n
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
                          pnames := ps.map (·.name), scope := copyScope? effs,
                          typeValues := ps.zipIdx.filterMap fun (param, i) => if param.typeValue then some i else none }
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
      let resolved ← resolveTParams env tps
      let resolved ← match ps.head? with
        | some receiver => do
          let unchecked := resolved.env { env with sbounds := [] }
          let ty ← (resolveTy unchecked p receiver.ty).run' { env := unchecked }
          match ty with
          | .struct owner args =>
            if ["Self", "$Self"].contains receiver.name && n.startsWith (owner ++ ".") then
              let σ := (((env.sparams.lookup owner).getD []).map (·.1)).zip args
              let extra := ((env.sbounds.lookup owner).getD []).map fun (base, derived) =>
                (SubtypeEvidence.Bound.mk base derived).subst σ
              pure { resolved with bounds := (resolved.bounds ++ extra).eraseDups }
            else pure resolved
          | _ => pure resolved
        | none => pure resolved
      let tparams := resolved.params
      let genv := resolved.env env
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
      let lifted := opts.requests.casts.find? (·.name == n)
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
          let dictionaryCall := m == "$apply" && c.startsWith "$choiceOperationDictionary"
          let resumeCall := opts.requests.loops.any (fun l => l.resumes.any (·.name == n))
          if effs.contains "override" && env.classes.contains c && env.isRefClass c &&
              (!m.startsWith "$" || valueCall || dictionaryCall || resumeCall) &&
              (match tys.head? with | some (.struct c' _) => c' == c | _ => false) then
            -- (#351: below an interface referred to through views, every
            -- type parameter, which a dispatch through a view may open)
            (if env.viewed.any (env.isSub c ·) then ((env.sparams.lookup c).getD []).map (·.1)
             else env.addedParams c).filter fun v => tparams.any (·.1 == v) && (env.witnessField? c v).isSome
          else []
        | _ => []
      -- generic functions come after the others
      let selfBounds := (tys.head?.map fun receiver =>
        SubtypeEvidence.fieldsForBounds env receiver resolved.bounds).getD []
      gsigs := gsigs.push { idx := tops.length + gidx, name := n, params := tys, ret := rt, selfTps,
                            decides := effs.contains "decides", isConst := false,
                            suspends := effs.contains "suspends",
                            -- (a parametric class's `block:`: inferred from none, #41)
                            fx := if n.endsWith ".$block" || defaultBridge n then [] else allowedFx effs,
                            tparams, bounds := resolved.bounds, selfBounds,
                            named := (ps.filter (·.named)).map fun q => (q.name, q.default),
                            pnames := ps.map (·.name), scope := copyScope? effs,
                            typeValues := ps.zipIdx.filterMap fun (param, i) => if param.typeValue then some i else none }
    | _ => pure ()
  let mkSigProg (sigs : Array Sig) : Prog :=
    { fns := (sigs ++ gsigs).toList.map fun s =>
        { name := s.name, arity := s.frame.arity, nslots := 0,
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
        match elabBody ctx body (some sigs[idx]!.ret) { env } with
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
          match elabBody ctx body (some sigs[idx]!.ret) { env } with
          | .ok (_, st) =>
            let fx := heapFx.filter fun k => st.fx.any (·.1 == k)
            if fx != sigs[idx]!.fx then
              sigs := sigs.set! idx { sigs[idx]! with fx }
              changed := true
          | .error _ => pure ()
        else if n.endsWith ".$block" || inferredBridge n then
          let s := sigs[idx]!
          let locals := (ps.zip (List.range ps.length)).zip s.params |>.map fun ((prm, i), t) =>
            ({ name := prm.name, slot := i, ty := t, mutable := false, typeValue := prm.typeValue } : Local)
          let base : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := env,
                              locals := locals.reverse, retTy := s.ret, canFail := s.decides, suspends := s.suspends, fnFx := s.fx }
          let ctx ← functionBodyCtx opts.requests base p n s.tparams s.scope
          match elabBody ctx body (some s.ret) { env, nslots := ps.length, slotTys := s.params.toArray, frameSlots := ctx.locals.filterMap fun l => l.storage.map (l.slot, ·) } with
          | .ok (_, st) =>
            let fx := heapFx.filter fun k => st.fx.any (·.1 == k) ||
              (opts.requests.casts.any (·.name == n) && s.fx.contains k)
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
            ({ name := prm.name, slot := i, ty := t, mutable := false, typeValue := prm.typeValue } : Local)
          let locals := locals ++ g.evidenceLocals
          let dictTps := g.tparams.filter (fun (v, _) => !g.selfTps.contains v) ++
            g.tparams.filter (fun (v, _) => g.selfTps.contains v)
          let hidden := g.frame.hiddenTypes
          let lifted := opts.requests.casts.find? (·.name == n)
          let selfField (v : String) := match lifted with
            | some l => (l.opened.lookup v).bind (env.witnessField? l.target ·)
            | none => env.witnessField? ((n.splitOn ".").headD "") v
          let genv := { g.typeEnv env with dictOrder := dictTps.map (·.1), selfWitness := g.selfTps.map fun v => (v, (selfField v).getD 0) }
          let base : Ctx := { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs, types := genv,
                              locals := locals.reverse, retTy := g.ret, canFail := g.decides, suspends := g.suspends,
                              dictBase := g.frame.witnessBase, dictVars := dictTps.map (·.1), fnFx := g.fx }
          let ctx ← functionBodyCtx opts.requests base p n g.tparams g.scope
          match elabBody ctx body (some g.ret)
              { env := genv, nslots := ps.length + hidden.length, slotTys := (g.params ++ hidden).toArray, frameSlots := ctx.locals.filterMap fun l => l.storage.map (l.slot, ·) } with
          | .ok (_, st) =>
            let fx := heapFx.filter fun k => st.fx.any (·.1 == k) ||
              (opts.requests.casts.any (·.name == n) && g.fx.contains k)
            if fx != g.fx then
              gsigs := gsigs.set! gi { g with fx }
              changed := true
          | .error _ => pure ()
      | _ => pure ()
    if !changed then break
  let sigProg := mkSigProg sigs
  checkSignatures env { tops, generics, sigs, gsigs, prog := sigProg } classes.defs fields methods
  let defaults ← elabFieldDefaults env { tops, generics, sigs, gsigs, prog := sigProg } methods.tops classes.defs
  -- (the accessors come right after the functions, #157)
  env := { env with fieldAccBase := tops.length + gsigs.size, signalNoRollback := opts.signalNoRollback }
  let genvOf (g : Sig) : TyEnv := g.typeEnv env
  let elaborated ← elabFunctions env { tops, generics, sigs, gsigs, prog := sigProg } opts.requests
  let mut fns := elaborated.map (·.fn)
  let mut slotTys := elaborated.map (·.slotTys)
  -- (where each function calls `Err()`, by its index, #235)
  let errs := elaborated.map (·.errAt)
  let frameInfo := elaborated.map (·.frames)
  let mut metadataInfo := elaborated.map (·.metadata)
  -- (the lazily taken functions with several values that contexts taking
  -- their first success consume, #246)
  let loopFirst := elaborated.toList.flatMap (·.loopFirst)
  let failCalls := elaborated.foldl (fun acc f => acc ++ f.failCalls) #[]
  let mut needs := elaborated.foldl (fun acc f => acc.merge f.needs) defaults.needs
  -- (#283) the eager groups, the families of the uses of methods whose
  -- receivers' classes this one found, and the overloads of the calls whose
  -- arguments' types it found; those it did not reach, of no family or
  -- overload, so that the last elaboration has none to find (and knows what
  -- can fail): the program is elaborated again with them, so this one goes
  -- no further
  if needs.families.isEmpty then needs := needs.merge { families := source.familySites.map fun (q, _) => (q, "") }
  if needs.overloads.isEmpty then needs := needs.merge { overloads := source.overloadSites.map fun (q, _) => (q, "") }
  -- (and the types of the names of consumers in recursive groups' code,
  -- whose groups this one kept with one value: `$noteTypes`)
  -- (and the field orders of the structs and classes those groups construct
  -- with a choice point in a field, `TyEnv.fieldOrder`)
  if !needs.eager.isEmpty || !needs.families.isEmpty || !needs.overloads.isEmpty || !source.nestedSites.isEmpty ||
      !source.fieldSites.isEmpty then
    return .asking { eager := needs.eager, families := needs.families, overloads := needs.overloads,
                     nested := needs.nested, fieldOrders := source.fieldSites.map fun n => (n, env.fieldOrder n) }
  -- (#214) and functions wanted as values at types no class of theirs
  -- gives, adapters for methods wanted as values, (#243) branches of casts
  -- that refine type arguments, lifted into functions, and helpers that
  -- forward calls to the defaults of their named parameters: likewise, as
  -- this one has placeholders for them
  if !needs.isEmpty then return .asking needs
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
      (spawnParamTypes genv g.name (g.frame.argumentTypes.map (Ty.toVTy genv)), g.ret.toVTy genv)
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
    metadataInfo := metadataInfo.push {}
    accSigs := accSigs.push ([selfTy], fTy)
    fns := fns.push { name := s!"{d}.$set.{f}", arity := 2, nslots := 2, decides := false, writes := true,
                      body := .heap (.set kd) [.local 0, .local 1] }
    slotTys := slotTys.push [selfTy, fTy]
    metadataInfo := metadataInfo.push {
      metadataWrites := if f.startsWith "$w." then [(0, kd)] else [] }
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
    metadataInfo := metadataInfo.modify gi fun info => { info with
      body := info.body.map (Suspend.pruneDead S00 ((slotTys[gi]?).getD [])) }
  -- (#235) the functions with several values computed at their calls
  let lazyNeeds ← checkEager fns errs (fun g => ((tops ++ generics).findSome? fun
    | .fn p n .. => if n == g then some p else none
    | _ => none)) opts.requests.lazy
  if !lazyNeeds.isEmpty then
    return .asking { lazy := lazyNeeds }
  -- (#515, `--signal-no-rollback`) no event signal from a failure context
  if opts.signalNoRollback then
    if let some ((p, what), way) := SignalAdmission.checkSites fns failCalls then
      throw s!"{p.show}: this {what} may signal an event ({" → ".intercalate way}) in a failure context, which --signal-no-rollback refuses: the published Verse API makes an event's Signal <no_rollback> (#515)"
  -- (#246) and functions of their own for the lazily taken calls whose
  -- effects need them: the program is elaborated again, with them
  let loopNeeds ← checkLoopFirst fns loopFirst opts.requests.loops
  if !loopNeeds.isEmpty then
    return .asking { loops := loopNeeds }
  if !opts.extendedDefaults then
    let ordinary := (tops ++ generics).filterMap fun
      | .fn _ n _ _ specs .. =>
        if specs.contains InitializerConvergence.sourceCallMarker then some n else none
      | _ => none
    let construction := classes.defs.filterMap fun cd =>
      if cd.methods.any (fun | .fn _ "$block" .. => true | _ => false) then
        some (cd.name ++ ".$block") else none
    let mut verified : Std.HashSet Nat := {}
    for (owner, field, pos, body) in defaults.bodies do
      match (InitializerConvergence.checkExpr fns ordinary (construction ++ admitted.intrinsicCalls) [] body).run verified with
      | .ok (_, checked) => verified := checked
      | .error reason =>
        throw s!"{pos.show}: default of field '{field}' of {owner} requires convergence: {reason} (#511; --extended-defaults retains the OpenVerse extension without a convergence assertion)"
  let metadataFields := env.classes.toArray.map fun c =>
    (env.fields c).zipIdx.filterMap fun ((name, _, _), i) =>
      if name.startsWith "$w." then some i else none
  MetadataFlow.check fns metadataInfo metadataFields opts.debug
  let (capturedFns, capturedSlots, capturedSigs) ← FailCapture.lower fns slotTys S00
  fns := capturedFns
  slotTys := capturedSlots
  let fsigs0 := capturedSigs.fns
  fsigs := fsigs0
  let beforeConcurrency := fns
  if admitted.usesConc then
    let (fns1, slotTys1, fsigs1, classTable1, frameClasses1, mainCall1, framePins1, schedMore) ←
      lowerOpening fun forced =>
        lowerConcurrency env sigs gsigs mainSig fsigs0 protos pins inFn fns slotTys fsigs classTable forced frameInfo
          opts.eventFifo
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
  if admitted.usesConc then
    fns := CompilerWrites.propagate beforeConcurrency fns
  -- (the frame classes' pins after the classes', #244)
  let pins := (List.range classTable.length).map (fun t => (pins[t]?).getD []) ++ framePins
  certify { prog := { fns := fns.toList, main },
            sigs := { fns := fsigs, classes := classTable ++ frameClasses.toList, protos, pins }, slotTys }
    methods.stubs opts.debug

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

/-- What an elaboration asks for (`Requests`) is of three tiers, by what it
    changes, and an elaboration asks for one tier at a time
    (`elabProgramCore` goes no further than the first it finds):
    1. how the source's choices are inlined (#283): eager groups, lazily
       taken functions, the families of methods' uses, the overloads of
       calls, the types of consumers' names in recursive groups' code and
       the field orders of what that code constructs;
    2. the classes' layout (#351): hidden fields for all of a class's type
       parameters;
    3. the functions added: functions as values (#214), method adapters, the
       branches of refining casts (#243), and the functions of lazily taken
       calls and the helpers of consumers of choices (#246, #335). -/
def Requests.tier (r : Requests) : Nat :=
  if !r.eager.isEmpty || !r.families.isEmpty || !r.overloads.isEmpty || !r.lazy.isEmpty || !r.nested.isEmpty ||
      !r.fieldOrders.isEmpty then 1
  else if !r.witnesses.isEmpty then 2
  else 3

/-- The requests of tier `k` and of the tiers above it (`Requests.tier`). -/
def Requests.upTo (r : Requests) (k : Nat) : Requests :=
  if k ≥ 3 then r else
  { eager := r.eager, families := r.families, overloads := r.overloads, lazy := r.lazy, nested := r.nested,
    fieldOrders := r.fieldOrders, witnesses := if k = 2 then r.witnesses else [] }

/-- Elaborate a parsed program (`elabProgramCore`), with the names of the
    functions a constructor or an overload becomes shown as written: `K$init`
    is `K<constructor>`, `F$ov1` is `F` (names with `$` are never the user's).

    It is elaborated in rounds: as long as an elaboration asks for something
    new, the program is elaborated again with it. A round that asks for more
    of one tier (`Requests.tier`) is followed by one with the requests of that
    tier and of the tiers above it only, as what the source or the classes
    are changes what the tiers below ask for: those are asked for again, and
    their budgets of rounds start again. -/
def elabProgram (allTops00 : List STop) (opts : Options := {}) : Except String Compiled :=
  let defaults := allTops00.foldl (fun n t => n + topDefaultCount t) 0
  let classes := allTops00.filter (fun | .classDef .. => true | _ => false) |>.length
  -- (tier 3: each round asks for new functions only, so a few rounds do)
  let rounds := max 4 (4 * (allTops00.foldl (fun n t => max n (topLiftDepth t)) 0 + defaults * (classes + 1)))
  -- (tier 2: each round asks for more classes' hidden fields)
  let witnessRounds := max 8 (classes + 1)
  -- (tier 1: each round notes the uses of methods it found, which may make
  -- more methods have several values, whose uses the next one notes. A
  -- restart discards helpers prepared for the lazy group; their bodies
  -- must be discovered again after its calls become eager. Each restart
  -- forces a new source function's group, so source definitions bound it.)
  let eagerRounds := allTops00.foldl (fun n t => n + match t with
    | .fn .. => 1
    | .classDef _ _ _ _ _ _ _ _ ms => ms.length
    | _ => 0) 1
  let rec loop (eagerFuel witnessFuel fuel : Nat) (req : Requests) : Except String Compiled := do
    let c ← elabProgramCore allTops00 { opts with requests := req }
    let new := c.needs.without req
    match c.needs.tier with
    | 1 =>
      match eagerFuel, new.isEmpty with
      | eagerFuel + 1, false => loop eagerFuel witnessRounds rounds ((req.upTo 1).merge new)
      | _, _ => throw "internal error: mutual generator instances or methods' families still changing after eager lowering (#283)"
    | 2 =>
      match witnessFuel with
      | witnessFuel + 1 => loop eagerFuel witnessFuel rounds ((req.upTo 2).merge new)
      | 0 => throw "internal error: classes still asking for hidden fields after several elaborations (#351)"
    | _ =>
      if new.isEmpty then
        if c.needs.isEmpty then return c
        -- (all asked for before: an elaboration asks for functions and
        -- methods only when they are not requested yet, and one that asks
        -- for anything has no program, `Compiled.asking`)
        if fuel == 0 then
          throw "internal error: casts that refine type arguments, or lazily taken calls, still to lift after several elaborations (#243, #246)"
        throw "internal error: a function as a value, a method adapter, a cast that refines type arguments, or a lazily taken call's function was asked for again (#214, #243, #246)"
      let newDefaults := new.loops.filter fun l => defaultBridge l.name
      match fuel with
      | 0 =>
        if !newDefaults.isEmpty then throw "internal error: default forwarding helpers still to infer after several elaborations"
        if !new.methods.isEmpty then throw "internal error: method variance adapters still to infer after several elaborations"
        -- (a program with a placeholder left is never given out)
        if !new.fns.isEmpty then throw "internal error: functions still wanted as values after several elaborations (#214)"
        throw "internal error: casts that refine type arguments, or lazily taken calls, still to lift after several elaborations (#243, #246)"
      | fuel + 1 =>
        if newDefaults.isEmpty then return ← loop eagerFuel witnessFuel fuel (req.merge new)
        -- A newly materialized dispatch-default helper can reveal heap effects
        -- absent from an earlier suffix trial. Rediscover consumers after those
        -- helpers have participated in effect inference; their cached stage
        -- interfaces, prefixes and resume methods must agree on permissions.
        -- Each restart retains the new bridges, so discovery still progresses.
        let bridges := req.loops.filter fun l => defaultBridge l.name || spawnAdapter l.name
        loop eagerFuel witnessFuel fuel { req.merge { fns := new.fns, methods := new.methods, subtypes := new.subtypes } with
          casts := [], loops := bridges ++ newDefaults }
  termination_by (eagerFuel, witnessFuel, fuel)
  (loop eagerRounds witnessRounds rounds opts.requests).mapError fun msg =>
    FnValues.pretty (((stripOv ((Refine.unmarked msg).replace "$init" "<constructor>")).replace "::" ".").replace "$replaceAll" "ReplaceAll")

/-- Parse and elaborate Verse source text. -/
def compileChecked (src : String) (opts : Options := {}) : Except String Compiled := do
  elabProgram (← parseProgram src) opts

/-- Parse and elaborate Verse source text. -/
def compile (src : String) (opts : Options := {}) : Except String Prog := do
  return (← compileChecked src opts).prog

/-- Compile loaded definitions (`Front.loadProgram`) with shell arguments,
    bound to `Args` when given or mentioned, and an optional `do` expression. -/
def compileTops (tops : List STop) (args : List String) (mentionsArgs : Bool) (doExpr : Option String)
    (debug : Bool := false) (profile : SourceProfile := .full) (eventFifo : Bool := false)
    (extendedDefaults : Bool := false) (signalNoRollback : Bool := false) : Except String Prog := do
  let entry ← match doExpr with
    | some t => some <$> parseExprText t
    | none => pure none
  let useArgs := !args.isEmpty || mentionsArgs
  let opts : Options := { args := if useArgs then some args else none, entry, debug, profile, eventFifo, extendedDefaults }
  return (← elabProgram tops { opts with signalNoRollback }).prog

/-- Compile with shell arguments (bound to `Args` when given or used) and an
    optional `do` expression, as `openverse run FILE ARG… do EXPR` does. -/
def compileWith (src : String) (args : List String) (doExpr : Option String)
    (profile : SourceProfile := .full) (extendedDefaults : Bool := false) : Except String Prog := do
  let entry ← match doExpr with
    | some t => some <$> parseExprText t
    | none => pure none
  let useArgs := !args.isEmpty || (src.splitOn "Args").length > 1
  compile src { args := if useArgs then some args else none, entry, profile, extendedDefaults }

end OpenVerse.Front
