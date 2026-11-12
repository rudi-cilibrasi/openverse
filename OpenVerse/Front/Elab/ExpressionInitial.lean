/- A contiguous expression-handler stage; fallthrough preserves source pattern order. -/
import OpenVerse.Front.Elab.Control

namespace OpenVerse.Front
open OpenVerse
set_option maxHeartbeats 800000 in
partial def elabExprInitialWith
    (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabOneClauses : Ctx → List SExpr → EM (R × Ctx))
    (elabSpawnBound : Ctx → Pos → String → String → List SExpr → EM R)
    (elabFieldDefault : Ctx → Pos → String → List Ty → String → Ty → SExpr → EM Expr)
    (elabConstruct : Ctx → Pos → String → List STy → List SExpr → Option Ty → EM R)
    (next : Ctx → SExpr → Option Ty → EM R)
    (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  match se with
  | .app _ (.ident _ "$typeValue") [value] false => elabE ctx value exp
  | .app p (.ident _ "$subtypeLift") (input :: dictionaries) false =>
    elabSubtypeLiftWith elabE ctx p input dictionaries exp
  | .app p (.ident _ "$subtypeWitness") [.construct _ "$subtypeEvidence" [base, derived] []] false =>
    let base ← resolveTy ctx.types p base
    let derived ← resolveTy ctx.types p derived
    let locals := ctx.evidenceTypes
    let bound : SubtypeEvidence.Bound := ⟨base, derived⟩
    -- The formal default check validates a compiler-owned proof field's
    -- declared relation. Its placeholder is discarded; construction must
    -- supply a real dictionary in the caller's current lexical context.
    if ctx.inDefaultCheck && ctx.defaults.any (fun (_, field) => field.startsWith SubtypeEvidence.fieldPrefix) &&
        ctx.types.boundSubtype derived base then
      return ⟨.prim .userErr [], bound.ty⟩
    let some plan := SubtypeEvidence.find? ctx.types locals bound
      | eerr p s!"type {derived.show} does not satisfy subtype({base.show})"
    elabSubtypeValueWith elabE ctx p plan bound
  | .app p (.ident _ "$choiceCoercions") [.block _ metadata, body] false =>
    let rules ← metadata.mapM fun
      | .tuple _ [.ident _ name, .construct _ "$choiceConversion" [source, target] []] => do
        let some dictionary := ctx.lookup name | eerr p "internal: missing choice conversion dictionary"
        return (dictionary, ← resolveTy ctx.types p source, ← resolveTy ctx.types p target)
      | _ => eerr p "internal: invalid choice conversion evidence"
    let inherited := ctx.choiceCoercions.map fun (dictionary, source, target) =>
      ({ dictionary with ty := dictionary.ty.subst ctx.types.tvars }, source.subst ctx.types.tvars, target.subst ctx.types.tvars)
    let rules := (rules ++ inherited).foldl (fun collected entry =>
      if collected.any (fun old => old.1.name == entry.1.name && old.2 == entry.2) then collected
      else collected ++ [entry]) ([] : List (Local × Ty × Ty))
    elabE { ctx with choiceCoercions := rules } body exp
  | .app p (.ident _ "$choiceDictionary") [factory@(.construct _ cls _ [])] false =>
    if !cls.startsWith "$choiceOperationDictionary" then eerr p "internal: invalid dictionary allocation"
    -- Only the generated dictionary object is an implementation effect.
    -- Its hidden witness fields contain no source expressions.
    let effects := (← get).fx
    let r ← elabE ctx factory exp
    modify fun st => { st with fx := effects }
    return r
  | .app p (.ident _ "$choiceGenericOperation")
      (.str _ [.text shape] :: .ident _ name :: .block _ metadata ::
        .construct _ "$choiceSignature" schema [] :: .block _ instances :: values) bracket =>
    let some dictionary := ctx.lookup name | eerr p "internal: no generic operation dictionary"
    let .struct family _ := dictionary.ty | eerr p "internal: invalid generic operation dictionary"
    if !ctx.typeOnly then
      return ← elabE ctx (.app p (.ident p (family ++ "$apply")) (.ident p name :: values) bracket) exp
    let some (_, effects) := FnValues.parseName shape | eerr p "internal: invalid generic operation shape"
    if effects.contains "suspends" && !ctx.suspends then eerr p "an operation dictionary suspends here"
    if effects.contains "decides" && !ctx.canFail then eerr p "an operation dictionary can fail here"
    let methodParameters ← metadata.mapM fun
      | .tuple _ [.str _ [.text n], .int _ b] => pure (n, b == 1, none)
      | .tuple _ [.str _ [.text n], .int _ b, .construct _ "$upperBound" [upper] []] => pure (n, b == 1, some upper)
      | _ => eerr p "internal: invalid operation method parameter"
    let methodVars := methodParameters.map fun (name, comparable, _) => (name, comparable)
    let methodNames := methodVars.map (·.1)
    let make (probeCtx : Ctx) : EM (Sig × List (String × Ty)) := do
      let types := { probeCtx.types with tvars := methodVars.map (fun (n, b) => (n, Ty.param n b)) ++ probeCtx.types.tvars }
      let unchecked := { types with sbounds := [] }
      let bounds ← methodParameters.filterMapM fun (name, comparable, upper) => do
        let some upper := upper | pure none
        return some (SubtypeEvidence.Bound.mk (← resolveTy unchecked p upper) (.param name comparable))
      let signature ← schema.mapM (resolveTy unchecked p)
      if signature.length != values.length + 1 then eerr p "internal: invalid operation signature"
      let boundTypes := bounds.flatMap fun b => [b.base, b.derived]
      let fixed := Ty.mergeParamBounds ((signature ++ boundTypes).flatMap Ty.paramsC) |>.filter (!methodNames.contains ·.1)
      let some parameters := choiceMethodTParams p methodVars bounds
        | eerr p "internal: unrepresentable operation method constraints"
      let fixedParams : List TParam := fixed.map fun (name, comparable) =>
        { pos := p, name, constraint := if comparable then "comparable" else "type" }
      let flags ← match checkTParams types (fixedParams ++ parameters) with
        | .ok flags => pure flags
        | .error message => eerr p message
      let methodVars := methodVars.map fun (name, old) => (name, old || (flags.lookup name).getD false)
      let strengthened := methodVars.map fun (name, comparable) => (name, Ty.param name comparable)
      let signature := signature.map (·.subst strengthened)
      let bounds := bounds.map (fun b => SubtypeEvidence.Bound.subst b strengthened)
      let bounded := { types with boundFacts := bounds.map (fun b => (b.base, b.derived)) ++ types.boundFacts }
      for ty in signature ++ boundTypes do
        match ty.checkBounds bounded with
        | .ok _ => pure ()
        | .error message => eerr p message
      let sig : Sig := {
        idx := 0, name := family ++ "$probe", params := signature.dropLast,
        ret := signature.getLast!, tparams := methodVars, decides := bracket, isConst := false,
        fx := allowedFx effects, suspends := effects.contains "suspends", bounds }
      return (sig, fixed.map fun (n, b) => (n, Ty.param n b))
    let (sig, fixed) ← make ctx
    let r ← elabGenericCallWith elabE { ctx with callInstanceProbe := some sig.name } p sig values exp (inst := fixed)
    let .tup arguments := r.ty | eerr p "internal: missing operation type arguments"
    let after ← get
    -- Return-directed inference must commute with specializing the
    -- receiver. A differing choice needs an instance-specific lowering.
    for entry in instances do
      let .block _ equations := entry | eerr p "internal: invalid operation instance"
      let mut substitution : List (String × Ty) := []
      let mut applies := true
      for equation in equations do
        let .tuple _ [.construct _ "$choiceVariable" [left] [], .construct _ "$choiceInstance" [right] []] := equation
          | eerr p "internal: invalid operation equation"
        let left ← resolveTy ctx.types p left
        let right ← resolveTy ctx.types p right
        match left with
        | .param n _ => substitution := substitution ++ [(n, right)]
        | _ => if left != right then applies := false
      if !applies then continue
      let actual := { ctx with
        types := { ctx.types with tvars := substitution ++ ctx.types.tvars },
        locals := ctx.locals.map fun l => { l with
          ty := l.ty.subst substitution,
          storage := l.storage.map fun s => { s with args := s.args.map (·.subst substitution) } } }
      let check ← tryCatch (do
        let (instanceSig, fixed) ← make actual
        let result ← elabGenericCallWith elabE { actual with callInstanceProbe := some instanceSig.name }
          p instanceSig values (exp.map (·.subst substitution)) (inst := fixed)
        return some result.ty) (fun _ => pure none)
      set after
      let expected := Ty.tup (arguments.map (·.subst substitution))
      if check.any (fun ty => reprStr ty != reprStr expected) || check.isNone then
        eerr p "operation inference depends on the receiver instance"
    let result := sig.ret.subst (methodNames.zip arguments)
    noteFx p (allowedFx effects) (some name)
    if effects.contains "suspends" then
      modify fun st => { st with
        pendingSuspendingCasts := st.pendingSuspendingCasts + 1,
        pendingWaitingCasts := st.pendingWaitingCasts + 1,
        pendingSourceSuspends := st.pendingSourceSuspends + 1 }
    return ⟨.prim .userErr [], result⟩
  | .app p (.ident _ "$choiceIndexedOperation") [shape, dictionary@(.ident _ name), index, object, validation, old, rhs] bracket =>
    let some binding := ctx.lookup name | eerr p "internal: no indexed operation dictionary"
    let .struct _ [keyTy, objectTy, oldTy, rhsTy, _] := binding.ty | eerr p "internal: invalid indexed operation signature"
    let keySlot ← fresh keyTy
    let objectSlot ← fresh objectTy
    let oldSlot ← fresh oldTy
    let rhsSlot ← fresh rhsTy
    let keyValue ← coerce p (← elabE ctx index (some keyTy)) keyTy
    let keyContext := { ctx with
      locals := { name := "$choiceIndexKey", slot := keySlot, ty := keyTy, mutable := false } :: ctx.locals }
    let objectValue ← coerce p (← elabE keyContext object (some objectTy)) objectTy
    let inner := { ctx with
      locals := { name := "$choiceIndexKey", slot := keySlot, ty := keyTy, mutable := false } ::
        { name := "$choiceIndexObject", slot := objectSlot, ty := objectTy, mutable := false } :: ctx.locals }
    let checked ← elabE inner validation none
    let oldValue ← coerce p (← elabE inner old (some oldTy)) oldTy
    let rhsValue ← coerce p (← elabE ctx rhs (some rhsTy)) rhsTy
    let final := { inner with
      locals := { name := "$choiceIndexOld", slot := oldSlot, ty := oldTy, mutable := false } ::
        { name := "$choiceIndexRHS", slot := rhsSlot, ty := rhsTy, mutable := false } :: inner.locals }
    let invocation := SExpr.app p (.ident p "$choiceOperation")
      [shape, dictionary, .ident p "$choiceIndexKey", .ident p "$choiceIndexObject",
        .ident p "$choiceIndexOld", .ident p "$choiceIndexRHS"] bracket
    let result ← elabE final invocation exp
    return ⟨.seq (.assign keySlot keyValue) (.seq (.assign objectSlot objectValue)
      (.seq checked.e (.seq (.assign oldSlot oldValue) (.seq (.assign rhsSlot rhsValue) result.e)))), result.ty⟩
  | .app p (.ident _ "$choiceOperation") (.str _ [.text shape] :: .ident _ name :: values) bracket =>
    let some dictionary := ctx.lookup name | eerr p "internal: no operation dictionary"
    let .struct family types := dictionary.ty | eerr p "internal: invalid operation dictionary"
    if types.length != values.length + 1 then eerr p "internal: invalid operation arity"
    let some (_, effects) := FnValues.parseName shape | eerr p "internal: invalid operation shape"
    if ctx.typeOnly then
      if effects.contains "suspends" && !ctx.suspends then eerr p "an operation dictionary suspends here"
      if effects.contains "decides" && !ctx.canFail then eerr p "an operation dictionary can fail here"
      for (value, input) in values.zip types.dropLast do
        discard <| coerce p (← elabE ctx value (some input)) input
      noteFx p (allowedFx effects) (some name)
      if effects.contains "suspends" then
        modify fun st => { st with
          pendingSuspendingCasts := st.pendingSuspendingCasts + 1,
          pendingWaitingCasts := st.pendingWaitingCasts + 1,
          pendingSourceSuspends := st.pendingSourceSuspends + 1 }
      return ⟨.prim .userErr [], types.getLast!⟩
    elabE ctx (.app p (.ident p (family ++ "$apply")) (.ident p name :: values) bracket) exp
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
      | .code e => do elabToStringWith elabE ctx e.pos (← elabE ctx e none)
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
  | _ => next ctx se exp

end OpenVerse.Front
