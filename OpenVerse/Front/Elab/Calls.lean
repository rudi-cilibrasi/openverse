/- Elaboration calls; public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Continuations

namespace OpenVerse.Front
open OpenVerse
/-- Bare type names written in a default, excluding names bound by a local
    generic struct. Parametric type heads name declarations, not aliases. -/
partial def defaultTypeNames (bound : List String) (e : SExpr) : List String :=
  let bare := fun (t : STy) => (t.bareNames.filter (!bound.contains ·))
  match e with
  | .structDef _ tps _ fs =>
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
    | .structDef p tps specs fs =>
      let σ' := σ.filter fun (n, _) => !tps.any (·.name == n)
      some (.structDef p tps specs (fs.map fun (n, t, d, v) =>
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

/-- Canonicalise the user positional arguments before binding a call. A
    receiver is not part of the argument tuple; named arguments retain their
    written order. A lone scalar keeps its meaning for arrays and bare type
    parameters. Empty arrays still require an explicit array value. -/
def packCallArgs (p : Pos) (s : Sig) (args : List SExpr)
    (hasReceiver : Bool := true) : List SExpr := Id.run do
  let isNamed : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
  let off := if hasReceiver && s.hasReceiver then 1 else 0
  let pos := args.filter (!isNamed ·)
  let user := pos.drop off
  let named := args.filter isNamed
  let [pt] := s.params.drop off |>.take (s.params.length - s.named.length - off)
    | return args
  let packed := fun a => pos.take off ++ [a] ++ named
  match pt with
  | .void => if user.isEmpty then return packed (.tuple p []) else return args
  | .tup _ =>
    if user.length != 1 then return packed (.tuple p user)
    if let .tup [_] := pt then
      let [a] := user | return args
      match a with
      | .tuple _ [_] | .app _ (.ident _ "$callSingleton") [_] false => return args
      | _ => return packed (.app a.pos (.ident a.pos "$callSingleton") [a] false)
    return args
  | .arr _ => if user.length > 1 then return packed (.arrayLit p user) else return args
  | .param .. => if user.length != 1 then return packed (.tuple p user) else return args
  | _ => return args

partial def elabSubtypeValueWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx)
    (p : Pos) (plan : SubtypeEvidence.Plan) (bound : SubtypeEvidence.Bound) : EM R := do
  let missing := plan.nominals.filter fun (source, target) =>
    !ctx.types.classes.contains (SubtypeEvidence.nominalFamily source target)
  let tuples := plan.tupleArities.filter fun arity =>
    !ctx.types.classes.contains (SubtypeEvidence.tupleFamily arity)
  let tupleArrays := plan.tupleArrayArities.filter fun arity =>
    !ctx.types.classes.contains (SubtypeEvidence.tupleArrayFamily arity)
  let refinements := plan.refinements.filter fun (source, target) =>
    !ctx.types.classes.contains (SubtypeEvidence.refinementFamily source target)
  if !missing.isEmpty || !tuples.isEmpty || !tupleArrays.isEmpty || !refinements.isEmpty then
    let declarations ← missing.mapM fun (source, target) =>
      match SubtypeEvidence.nominal ctx.types p source target with
      | .ok declaration => pure declaration
      | .error message => eerr p message
    let declarations := declarations ++ tuples.map (SubtypeEvidence.tupleDeclaration p)
    let declarations ← tupleArrays.foldlM (fun declarations arity =>
      match SubtypeEvidence.tupleArrayDeclaration p arity with
      | .ok declaration => pure (declarations ++ [declaration])
      | .error message => eerr p message) declarations
    let declarations ← refinements.foldlM (fun declarations (source, target) =>
      match SubtypeEvidence.refinementDeclaration ctx.types p source target with
      | .ok declaration => pure (declarations ++ [declaration])
      | .error message => eerr p message) declarations
    modify fun state => { state with subtypeNeeds := SubtypeEvidence.mergeRequests state.subtypeNeeds declarations }
    return ⟨.prim .userErr [], bound.ty⟩
  elabE ctx (plan.value ctx.types p) (some bound.ty)

/-- Compiler-owned container Up bodies. Every component conversion is an
    ordinary checked call on an explicitly supplied dictionary. The input
    and dictionaries are saved once; traversal preserves array/map order,
    map entry order (even duplicate keys), option absence and tuple shape. No
    runtime cast or map reconstruction is involved. -/
partial def elabSubtypeLiftWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx)
    (p : Pos) (input : SExpr) (dictionaries : List SExpr) (exp : Option Ty) : EM R := do
  let some target := exp | eerr p "internal: a subtype lift requires its declared result"
  let value ← elabE ctx input none
  let inputSlot ← fresh value.ty
  let (components, traversal) ← match value.ty, target with
    | .arr c, .arr a | .opt c, .opt a => do
      let element ← fresh c
      pure ([(SubtypeEvidence.Bound.mk a c, Expr.local element)], some element)
    | .map k c, .map l a => do
      if !isComparable ctx.types k || !isComparable ctx.types l then
        eerr p "internal: subtype map keys must be comparable"
      let element ← fresh (.tup [k, c])
      pure ([(SubtypeEvidence.Bound.mk l k, Expr.prim (.tupGet 0) [.local element]),
        (SubtypeEvidence.Bound.mk a c, Expr.prim (.tupGet 1) [.local element])], some element)
    | .tup cs, .tup bases => do
      if cs.length != bases.length then eerr p "internal: subtype tuple arities differ"
      pure ((bases.zip cs).zipIdx.map (fun ((a, c), i) =>
        (SubtypeEvidence.Bound.mk a c, Expr.prim (.tupGet i) [.local inputSlot])), none)
    | .tup cs, .arr a => do
      if cs.isEmpty then eerr p "internal: an empty tuple is not a tuple-to-array subtype"
      pure (cs.zipIdx.map (fun (c, i) =>
        (SubtypeEvidence.Bound.mk a c, Expr.prim (.tupGet i) [.local inputSlot])), none)
    | _, _ => eerr p "internal: unsupported subtype container shape"
  if components.length != dictionaries.length then eerr p "internal: missing subtype component dictionaries"
  let mut setup : List (Nat × Expr) := [(inputSlot, value.e)]
  let mut outputs : List Expr := []
  for ((bound, operand), dictionary) in components.zip dictionaries do
    if ctx.isTypeValue dictionary then eerr p "internal: a dummy type value is not subtype evidence"
    let proof ← elabE ctx dictionary (some bound.ty)
    let proofExpr ← coerce p proof bound.ty
    let proofSlot ← fresh bound.ty
    let componentSlot ← fresh bound.derived
    let proofName := s!"$subtypeLiftProof{proofSlot}"
    let componentName := s!"$subtypeLiftValue{componentSlot}"
    let inner := { ctx with locals :=
      { name := proofName, slot := proofSlot, ty := bound.ty, mutable := false } ::
      { name := componentName, slot := componentSlot, ty := bound.derived, mutable := false } :: ctx.locals }
    let result ← elabE inner (.app p (.member p (.ident p proofName) "Up")
      [.ident p componentName] false) (some bound.base)
    setup := setup ++ [(proofSlot, proofExpr)]
    outputs := outputs ++ [.seq (.assign componentSlot operand) (← coerce p result bound.base)]
  let body ← match value.ty, target, traversal, outputs with
    | .arr _, .arr _, some element, [output] =>
      pure (.forE element (.local inputSlot) (.lit (.logic true)) output)
    | .opt _, .opt _, some element, [output] =>
      pure (.ite (.assign element (.prim .query [.local inputSlot]))
        (.prim .mkSome [output]) (.lit .none))
    | .map _ _, .map _ _, some element, [key, output] =>
      pure (.forE element (.local inputSlot) (.lit (.logic true))
        (.prim .mkTup [key, output]))
    | .tup _, .tup _, none, _ => pure (.prim .mkTup outputs)
    | .tup _, .arr _, none, _ => pure (.prim .mkArr outputs)
    | _, _, _, _ => eerr p "internal: invalid subtype traversal"
  return ⟨setup.foldr (fun (slot, expression) rest => .seq (.assign slot expression) rest) body, target⟩

partial def elabSubtypeUpWith (elabE : Ctx → SExpr → Option Ty → EM R)
    (ctx : Ctx) (p : Pos) (value : R) (target : Ty) (plan : SubtypeEvidence.Plan) : EM R := do
  let locals := ctx.evidenceTypes
  if !plan.valid ctx.types locals || plan.bound ctx.types != ⟨target, value.ty⟩ then
    eerr p "internal: subtype view has no valid lexical evidence"
  let slot ← fresh value.ty
  let name := s!"$subtypeInput{slot}"
  let inner := { ctx with locals := { name, slot, ty := value.ty, mutable := false } :: ctx.locals }
  let dictionary ← elabSubtypeValueWith elabE ctx p plan ⟨target, value.ty⟩
  let dictionarySlot ← fresh dictionary.ty
  let dictionaryName := s!"$subtypeDictionary{dictionarySlot}"
  let inner := { inner with locals :=
    { name := dictionaryName, slot := dictionarySlot, ty := dictionary.ty, mutable := false } :: inner.locals }
  let call := SExpr.app p (.member p (.ident p dictionaryName) "Up") [.ident p name] false
  let result ← elabE inner call (some target)
  return ⟨.seq (.assign slot value.e) (.seq (.assign dictionarySlot dictionary.e)
    (← coerce p result target)), target⟩

partial def elabBoundReceiverWith (elabE : Ctx → SExpr → Option Ty → EM R)
    (ctx : Ctx) (p : Pos) (value : R) (member : String) : EM R := do
  let view ← match ctx.boundView p value.ty member with
    | .ok view => pure view
    | .error message => throw message
  let some target := view | return value
  let locals := ctx.evidenceTypes
  let some plan := SubtypeEvidence.find? ctx.types locals ⟨target, value.ty⟩
    | eerr p "internal: a bound view lost its lexical dictionary"
  elabSubtypeUpWith elabE ctx p value target plan

/-- A call of a generic function. Its type arguments are inferred by matching
    its signature: the result type against the expected type (unless that is
    `void`, which accepts anything), then each parameter type against its
    argument's, left to right. An argument whose parameter type is already
    determined is elaborated against it, so `array{}` and `false` work. -/
partial def elabGenericCallWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (p : Pos) (s : Sig) (args : List SExpr) (exp : Option Ty)
    (packArgs : Bool := false) (inst : List (String × Ty) := []) (resultRetry : Bool := true) :
    EM R := do
  -- A partially inferred result may suggest a type that later violates a
  -- bound. Retry argument/default inference from the original compiler
  -- state, preserving explicit instances and reporting the original error
  -- if neither trial works. Source arguments are still evaluated once.
  if resultRetry && !s.bounds.isEmpty && exp.isSome then
    let before ← get
    return ← tryCatch (elabGenericCallWith elabE ctx p s args exp packArgs inst false) fun original => do
      set before
      tryCatch (elabGenericCallWith elabE ctx p s args none packArgs inst false) fun _ => throw original
  let args := packCallArgs p s args
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
  for (argument, index) in given do ctx.checkArgumentRole s argument index
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
      if let some σ' := s.ret.matchArg ctx.types σ et then
        if s.bounds.isEmpty || SubtypeEvidence.acceptsKnownBounds ctx.evidenceEnv s.bounds σ' then σ := σ'
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
          if !s.bounds.isEmpty then
            let some inferred := SubtypeEvidence.infer ctx.evidenceEnv s.bounds σ
              | eerr a.pos s!"cannot infer nominal bound arguments of {s.name}"
            σ := inferred
          if pass == 0 && !bound σ pt then
            deferred := deferred.set! i true
          else
            es := es.set! i (← coerce a.pos r (pt.subst σ))
        | none => eerr a.pos s!"expected {(pt.subst σ).show}, found {r.ty.show} (in a call of {s.name})"
  -- the arguments, in their temporaries, then the defaults
  let inferred ← match SubtypeEvidence.infer (if s.bounds.isEmpty then ctx.types else ctx.evidenceEnv) s.bounds σ with
    | some inferred => pure inferred
    | none => eerr p s!"cannot infer a consistent upper-bound instance of {s.name}"
  σ := inferred
  let mut steps : Array Expr := #[]
  let mut slots : Array (Option Nat) := Array.replicate s.params.length none
  let mut roles : Array Bool := s.params.toArray.mapIdx fun index _ => s.typeValues.contains index
  let mut defaultEvidence : List (SubtypeEvidence.Bound × Local) := []
  if !plain then
    for ((argument, k), i) in given.zip (List.range given.length) do
      let ta ← fresh (ptys[k]!.subst σ)
      steps := steps.push (.assign ta es[i]!)
      slots := slots.set! k (some ta)
      roles := roles.set! k (roles[k]! || ctx.isTypeValue argument)
    for ((n, dflt), j) in s.named.zip (List.range s.named.length) do
      let k := npos + j
      if slots[k]!.isNone then
        let some d := dflt | eerr p s!"{s.name} needs the argument ?{n}, which has no default"
        let pt := ptys[k]!
        -- (the default sees the parameters before it, in their temporaries)
        let earlier : List Local := ((s.pnames.zip (List.range k)).filterMap fun (pn, j) =>
          (slots[j]!).map fun sl => ({ name := pn, slot := sl, ty := ptys[j]!.subst σ, mutable := false, typeValue := roles[j]! } : Local)).reverse
        -- A named default sees the callee's declared relations at this
        -- actual instance, never arbitrary caller source names. Resolve
        -- actual dictionaries now, save them in fresh current-frame slots,
        -- and reuse those same values for the final call's proof arguments.
        for declared in s.bounds do
          if !(declared.base.params ++ declared.derived.params).all (fun name => (σ.lookup name).isSome) then continue
          let required := declared.subst σ
          if defaultEvidence.any (·.1 == required) then continue
          let proofCtx := { ctx with locals := defaultEvidence.map (·.2) ++ earlier ++ ctx.locals }
          let some plan := SubtypeEvidence.find? proofCtx.types proofCtx.evidenceTypes required | continue
          if !plan.valid proofCtx.types proofCtx.evidenceTypes then eerr p "internal: invalid default subtype evidence"
          let proof ← elabSubtypeValueWith elabE proofCtx p plan required
          let slot ← fresh required.ty
          steps := steps.push (.assign slot (← coerce p proof required.ty))
          let saved : Local := {
            name := s!"$subtypeDefault_{s.name}_{slot}", slot, ty := required.ty, mutable := false }
          defaultEvidence := defaultEvidence ++ [(required, saved)]
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
        let dctx := { ctx with locals := defaultEvidence.map (·.2) ++ earlier, selfClass := selfC,
                               selfMethod := if selfC.isSome then (s.name.splitOn ".").getLast? else none,
                               inParamDefault := true,
                               types,
                               inLoop := false, canFail := ctx.canFail && s.decides,
                               suspends := ctx.suspends && s.suspends,
                               defaults := key :: ctx.defaults }
        -- (its type: the parameter's, or what the default gives a type
        -- parameter nothing else determined)
        let σ0 := σ
        dctx.checkArgumentRole s d k
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
        roles := roles.set! k (roles[k]! || dctx.isTypeValue d)
  let inferred ← match SubtypeEvidence.infer (if s.bounds.isEmpty then ctx.types else ctx.evidenceEnv) s.bounds σ true with
    | some inferred => pure inferred
    | none => eerr p s!"cannot infer a consistent upper-bound instance of {s.name}"
  σ := inferred
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
  -- Prove every relation at this call's actual types. Keep evidence in
  -- lexical form until ordinary elaboration resolves the current frame.
  let evidencePlans ← s.frame.callBounds.mapM fun (_, required) => do
    let required := required.subst σ
    let locals := ctx.evidenceTypes
    let some plan := SubtypeEvidence.find? ctx.types locals required
      | eerr p s!"type {required.derived.show} does not satisfy subtype({required.base.show}) in a call of {s.name}"
    if !plan.valid ctx.types locals then eerr p "internal: invalid subtype evidence plan"
    return (required, plan)
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
  let evidence ← evidencePlans.mapM fun (required, plan) => do
    if let some (_, saved) := defaultEvidence.find? (·.1 == required) then return Expr.local saved.slot
    coerce p (← elabSubtypeValueWith elabE ctx p plan required) required.ty
  if plain then return ⟨.call s.idx (es.toList ++ evidence ++ dicts), s.ret.subst σ⟩
  let call := Expr.call s.idx (slots.toList.map (fun o => Expr.local o.get!) ++ evidence ++ dicts)
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

end OpenVerse.Front
