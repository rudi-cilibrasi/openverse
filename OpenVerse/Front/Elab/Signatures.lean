/- Elaboration of a program's signatures (phases 10–12 of `elabProgramCore`); public
   declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Classes

namespace OpenVerse.Front
open OpenVerse

/-- The overloads (`functionOverloads`). -/
structure Overloads where
  /-- The functions and constants (not the type definitions), each overloaded
      function renamed by its place among its overloads, `F$ovN`. -/
  tops : List STop
  /-- Each overloaded function's overloads (`TyEnv.overloads`). -/
  functions : List (String × List String)
  /-- Each overloaded method's overloads (`TyEnv.methodOverloads`), as many as
      it has parameter lists in a hierarchy at most (#106). -/
  methods : List (String × List String)

/-- Overloading (#74), a phase of `elabProgramCore`: the functions of one name
    among `allTops`, each renamed `F$ovN` (not `Main`, a built-in's name, or a
    name another definition has), and the overloads of the functions and of
    the methods (`methodOverloads`, #106). -/
def functionOverloads (env : TyEnv) (allTops : List STop) (methodOverloads : MethodOverloads) :
    Except String Overloads := do
  -- the type definitions: `name := struct …` and `name := enum …`
  let isTypeDef : STop → Bool
    | .const _ _ none (.structDef ..) | .const _ _ none (.enumDef ..) | .const _ _ none (.refineDef ..) => true
    | _ => false
  let tops := allTops.filter (!isTypeDef ·)
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
  return { tops, functions := ovMap,
           methods :=
             let bases := (methodOverloads.lists.map (·.1.2)).eraseDups
             bases.map fun mn =>
               let n := (methodOverloads.lists.filter (·.1.2 == mn)).foldl (fun acc (_, sigs) => max acc sigs.length) 0
               (mn, (List.range n).map fun k => s!"{mn}$ov{k}") }

/-- The functions and constants of a program and their signatures as declared
    (`declareSignatures`). -/
structure Declared where
  /-- The functions and constants, by index. -/
  tops : List STop
  /-- The generic functions, numbered after `tops`. -/
  generics : List STop
  /-- The signatures of `tops`, by index: an unannotated constant's type and the
      effects of a constant, a `block:` and a bridge not known yet. -/
  sigs : Array Sig
  /-- The signatures of `generics`, over their type parameters. -/
  gsigs : Array Sig

/-- Signatures, a phase of `elabProgramCore`: the generic functions (those with
    a `where` clause) apart, numbered after the others; no name defined twice
    or a built-in's; and each function's parameter and result types and
    effects, from its annotations, which must be consistent (#156), over its
    type parameters and their bounds for a generic one, with the type
    parameters it reads from its receiver's hidden fields (#209, #250, #351). -/
def declareSignatures (env : TyEnv) (tops : List STop) (requests : Requests) :
    Except String Declared := do
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
  -- a function's effects that exclude each other: at most one of <converges>,
  -- <computes> and <transacts>, and <computes> with no heap effect
  let checkExclusive (p : Pos) (n : String) (effs : List String) : Except String Unit := do
    if (["converges", "computes", "transacts"].filter effs.contains).length > 1 then
      throw s!"{p.show}: {n} has more than one of <converges>, <computes> and <transacts> (they exclude each other)"
    if effs.contains "computes" && ("transacts" :: heapFx).any effs.contains then
      throw s!"{p.show}: <computes> excludes the heap effects (<reads>, <writes>, <allocates>, <transacts>) that {n} also has"
  -- signatures: functions from their annotations, constants from theirs or by inference
  let mut sigs : Array Sig := #[]
  for (top, idx) in tops.zip (List.range tops.length) do
    match top with
    | .fn p n ps _ effs ret _ =>
      let (tys, rt) ← fnTypes env p n ps effs ret
      checkExclusive p n effs
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
      checkExclusive p n effs
      -- (#209) a method of a class with type parameters that its parent's
      -- type arguments do not give reads their values from its receiver
      -- (an overriding implementation: what a dispatch that opens them
      -- reaches; the class's other methods are called at known types)
      -- (#250: the function a cast's branch is lifted into, from the object,
      -- the cast's subject, its first parameter)
      let lifted := requests.casts.find? (·.name == n)
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
          let resumeCall := requests.loops.any (fun l => l.resumes.any (·.name == n))
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
  return { tops, generics, sigs, gsigs }

/-- The functions and constants of a program and their signatures, with the
    types of unannotated constants and the effects that are inferred known. -/
structure Signatures where
  /-- The functions and constants, by index (each overload a function of its
      own, `F$ovN`, #74). -/
  tops : List STop
  /-- The generic functions (those with a `where` clause), numbered after `tops`. -/
  generics : List STop
  /-- The signatures of `tops`, by index. -/
  sigs : Array Sig
  /-- The signatures of `generics`, over their type parameters. -/
  gsigs : Array Sig
  /-- The program calls are elaborated against (`Ctx.sigProg`), for what a call
      can do (`Expr.mayFail`, `Expr.writesHeap`): `sigs`, then `gsigs`. -/
  prog : Prog

/-- Every signature: the functions' and constants', then the generic functions'. -/
def Signatures.all (s : Signatures) : List Sig := s.sigs.toList ++ s.gsigs.toList

/-- The defaults function types write (#503, `STop.isTypeDefault`): each
    checked at its parameter's type with literals and top-level names only,
    as the pinned Book says nothing of what else one may use, in a trial that
    keeps nothing: a default is not part of its type and never runs. -/
def checkTypeDefaults (ctx : Ctx) (defaults : List STop) : Except String Unit := do
  for top in defaults do
    let .const p n (some ty) d := top | continue
    let param := ((n.splitOn typeDefaultPrefix).getLast?).getD n
    let trial : EM Unit := do
      let t ← resolveTy ctx.types p ty
      let r ← elabE ctx d (some t)
      if r.e.mayFail ctx.sigProg then eerr p "it can fail"
      discard <| coerce p r t
    if let .error e := trial.run { env := ctx.types } then
      throw s!"{e} (the default of ?{param} in a function type: not part of the type, it is checked at the parameter's type, with literals and top-level names only, #503)"

/-- Constant types and effects (#35), a phase of `elabProgramCore`: the type of
    each unannotated constant, inferred in rounds so that one may use one
    defined after it (the first still unknown refused); and the heap effects of
    constants, of `block:`s, of the defaults an overloaded constructor fills
    in (#99) and of bridges, inferred in rounds from none, as they use each
    other; between them, the defaults function types write (`checkTypeDefaults`). -/
def inferSignatures (env : TyEnv) (declared : Declared) (typeDefaults : List STop) (requests : Requests) :
    Except String Signatures := do
  let mut sigs := declared.sigs
  let mut gsigs := declared.gsigs
  -- A cast discovered before a default helper must acquire the helper
  -- effects once its body is known, before checking the source caller.
  let inferredBridge (n : String) := defaultBridge n || requests.casts.any (·.name == n)
  let mkSigProg (sigs gsigs : Array Sig) : Prog :=
    { fns := (sigs ++ gsigs).toList.map fun s =>
        { name := s.name, arity := s.frame.arity, nslots := 0,
          decides := s.decides, writes := s.fx.contains "writes", body := .lit .void },
      main := 0 }
  -- (the context each elaboration here starts from, under the signatures so far)
  let ctxOf (sigs gsigs : Array Sig) (types : TyEnv) : Ctx :=
    { sigs := sigs.toList ++ gsigs.toList, sigProg := mkSigProg sigs gsigs, types }
  -- infer the types of unannotated constants: in order, in rounds, so that a
  -- constant may use one defined after it (until a round makes no progress)
  let unannotated := (declared.tops.zip (List.range declared.tops.length)).filter fun
    | (.const _ _ none _, _) => true
    | _ => false
  let mut todo := unannotated
  for _ in [0:unannotated.length + 1] do
    let mut left := #[]
    for (top, idx) in todo do
      match top with
      | .const _ _ _ body =>
        let ctx := ctxOf sigs gsigs env
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
      let ctx := ctxOf sigs gsigs env
      let (r, _) ← (elabE ctx body none).run { env }
      if r.ty == .never then throw s!"{p.show}: cannot infer the type of '{n}'"
    | _ => pure ()
  checkTypeDefaults (ctxOf sigs gsigs env) typeDefaults
  -- the heap effects of a constant are those of its initialiser (#35), which
  -- runs at each use: in rounds, from none, since constants use each other
  for _ in [0:declared.tops.length + declared.generics.length + 1] do
    let mut changed := false
    for (top, idx) in declared.tops.zip (List.range declared.tops.length) do
      match top with
      | .const _ _ _ body =>
        let ctx := ctxOf sigs gsigs env
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
          let ctx := ctxOf sigs gsigs env
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
          let base : Ctx := { ctxOf sigs gsigs env with
                              locals := locals.reverse, retTy := s.ret, canFail := s.decides, suspends := s.suspends, fnFx := s.fx }
          let ctx ← functionBodyCtx requests base p n s.tparams s.scope
          match elabBody ctx body (some s.ret) { env, nslots := ps.length, slotTys := s.params.toArray, frameSlots := ctx.locals.filterMap fun l => l.storage.map (l.slot, ·) } with
          | .ok (_, st) =>
            let fx := heapFx.filter fun k => st.fx.any (·.1 == k) ||
              (requests.casts.any (·.name == n) && s.fx.contains k)
            if fx != s.fx then
              sigs := sigs.set! idx { s with fx }
              changed := true
          | .error _ => pure ()
      | _ => pure ()
    -- and so do those of a parametric class, generic (#39)
    for (top, gi) in declared.generics.zip (List.range declared.generics.length) do
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
          let lifted := requests.casts.find? (·.name == n)
          let selfField (v : String) := match lifted with
            | some l => (l.opened.lookup v).bind (env.witnessField? l.target ·)
            | none => env.witnessField? ((n.splitOn ".").headD "") v
          let genv := { g.typeEnv env with dictOrder := dictTps.map (·.1), selfWitness := g.selfTps.map fun v => (v, (selfField v).getD 0) }
          let base : Ctx := { ctxOf sigs gsigs genv with
                              locals := locals.reverse, retTy := g.ret, canFail := g.decides, suspends := g.suspends,
                              dictBase := g.frame.witnessBase, dictVars := dictTps.map (·.1), fnFx := g.fx }
          let ctx ← functionBodyCtx requests base p n g.tparams g.scope
          match elabBody ctx body (some g.ret)
              { env := genv, nslots := ps.length + hidden.length, slotTys := (g.params ++ hidden).toArray, frameSlots := ctx.locals.filterMap fun l => l.storage.map (l.slot, ·) } with
          | .ok (_, st) =>
            let fx := heapFx.filter fun k => st.fx.any (·.1 == k) ||
              (requests.casts.any (·.name == n) && g.fx.contains k)
            if fx != g.fx then
              gsigs := gsigs.set! gi { g with fx }
              changed := true
          | .error _ => pure ()
      | _ => pure ()
    if !changed then break
  return { tops := declared.tops, generics := declared.generics, sigs, gsigs, prog := mkSigProg sigs gsigs }

/-- The signature checks, a phase of `elabProgramCore`: the overloads of a
    function take parameters no call fits two of (Book of Verse ch. 6), and so
    do the overloads of a method a class sees (#106); an override has the
    signature of the method it overrides, is `<suspends>` as it is and allows
    no effect it does not (ch. 10); the implementation a concrete class uses
    has the signature of every declaration of the method above it, also at the
    declaring class's type arguments (#39, #53, #142, #351); an overriding field
    has the inherited field's type; and, last, no field has two interfaces'
    defaults (`Fields.defaultClashes`). -/
def checkSignatures (env : TyEnv) (sigs : Signatures) (cdefs : List CDef) (fields : Fields)
    (methods : Methods) : Except String Unit := do
  let allSigs := sigs.all
  -- overloads take parameters no call fits both of (Book of Verse ch. 6)
  let sigNamed (s : Sig) : List (String × Bool × Ty) :=
    let npos := s.params.length - s.named.length
    (s.named.zip (s.params.drop npos)).map fun ((n, d), t) => (n, d.isSome, t)
  let sigsDistinct (sa sb : Sig) : Bool :=
    let pa := sa.params.take (sa.params.length - sa.named.length)
    let pb := sb.params.take (sb.params.length - sb.named.length)
    let ba := sa.bounds.map fun bound => (bound.base, bound.derived)
    let bb := sb.bounds.map fun bound => (bound.base, bound.derived)
    env.paramsDistinct pa pb ba bb || env.namedDistinct (sigNamed sa) (sigNamed sb) ba bb
  for (n, ms) in env.overloads do
    for (a, i) in ms.zip (List.range ms.length) do
      for b in ms.take i do
        match allSigs.find? (·.name == a), allSigs.find? (·.name == b) with
        | some sa, some sb =>
          if !sigsDistinct sa sb then
            let pos := ((sigs.tops ++ sigs.generics).findSome? fun | .fn q m .. => if m == a then some q else none | _ => none).getD { line := 0, col := 0 }
            let sh (s : Sig) := ", ".intercalate ((s.params.zip (List.range s.params.length)).map fun (t, i) =>
              let npos := s.params.length - s.named.length
              if i < npos then t.show else s!"?{((s.named.drop (i - npos)).head?.map (·.1)).getD "?"}:{t.show}")
            throw s!"{pos.show}: {n} is defined twice with parameters a call cannot tell apart, ({sh sb}) and ({sh sa}): overloads must take disjoint types"
        | _, _ => pure ()
  -- the overloads of a method a class sees take parameters no call fits two
  -- of (#106: a subclass's new overload too; an override has its method's)
  for c in env.classes do
    let classArgs := ((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k
    let receiverBounds := ((env.sbounds.lookup c).getD []).map fun (base, derived) =>
      SubtypeEvidence.Bound.mk base derived
    let methodDomain (owner : String) (sg : Sig) : Sig :=
      let formals := (env.sparams.lookup owner).getD []
      -- Receiver formals share this class's scope. Method formals belong
      -- to the inherited declaration and must not capture those names.
      let own := sg.tparams.drop formals.length
      let renames := own.zipIdx.map fun ((v, k), i) =>
        (v, Ty.param s!"$overloadDomain{sg.idx}_{i}" k)
      let σ := (formals.map (·.1)).zip (env.upArgs c classArgs owner) ++ renames
      { sg with
        params := (sg.params.drop 1).map (·.subst σ)
        bounds := sg.bounds.map (·.subst σ) ++ receiverBounds }
    for (mn, ms) in env.methodOverloads do
      let vis : List (String × Sig) := ms.filterMap fun o =>
        ((env.supers c).find? fun e => allSigs.any (·.name == s!"{e}.{o}")).bind fun e =>
          (allSigs.find? (·.name == s!"{e}.{o}")).map fun sg => (s!"{e}.{o}", methodDomain e sg)
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
    let boundsA := (a.methodBounds ((env.sparams.lookup ea).getD []).length).map fun bound =>
      ({ base := inA bound.base, derived := inA bound.derived } : SubtypeEvidence.Bound)
    let boundsB := (b.methodBounds ((env.sparams.lookup eb).getD []).length).map fun bound =>
      ({ base := inB bound.base, derived := inB bound.derived } : SubtypeEvidence.Bound)
    oa.length == ob.length && (oa.map (·.2)) == (ob.map (·.2)) &&
    boundsA.length == boundsB.length && boundsA.all boundsB.contains && boundsB.all boundsA.contains &&
    a.typeValues == b.typeValues &&
    ((a.params.drop 1).map inA) == ((b.params.drop 1).map inB) &&
      retBelow (inA a.ret) (inB b.ret) && a.decides == b.decides &&
      a.named.map (·.1) == b.named.map (·.1)
  -- an implementation has no heap effect its declaration does not allow
  let fxOver (a b : Sig) : Option String := a.fx.find? (!b.fx.contains ·)
  for (mp, mine, theirs) in methods.overridePairs do
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
  for (cp, c, impl, decl) in methods.implChecks do
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
  for (fp, cname, f, sty) in fields.overrides do
    let cenv := { env with
      tvars := ((env.sparams.lookup cname).getD []).map fun (v, c) => (v, Ty.param v c)
      boundFacts := (env.sbounds.lookup cname).getD [] }
    let (t, _) ← (resolveTy cenv fp sty).run {}
    match fieldIndex (env.fields cname) f with
    | some (_, t0) =>
      if !(t == t0) then
        throw s!"{fp.show}: field '{f}' of {cname} must have the type it inherits, {t0.show}, not {t.show}"
    | none => pure ()
  if let some msg := fields.defaultClashes[0]? then throw msg

end OpenVerse.Front
