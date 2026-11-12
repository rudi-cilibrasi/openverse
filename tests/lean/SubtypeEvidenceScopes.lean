import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front OpenVerse.Front.SubtypeEvidence

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def getOK (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{label}: {message}")

private def refused (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .error message => need s!"{label}: wrong refusal: {message}" ((message.splitOn "does not satisfy subtype(vehicle)").length > 1)
  | .ok _ => throw (IO.userError s!"{label}: expected refusal")

private def p : Pos := { line := 1, col := 1, file := "evidence-scopes.verse" }

def main : IO Unit := do
  let t := Ty.param "t" false
  let u := Ty.param "u" false
  let vehicle := Ty.struct "vehicle" []
  let proof := (Bound.mk vehicle t).ty
  let box := Ty.struct "bounded_box" [t]
  let field := fieldName "bounded_box" "t"
  let env : TyEnv := {
    classes := ["vehicle", "car", "bounded_box", family]
    structs := [("vehicle", []), ("car", []), (family, []),
      ("bounded_box", [("X", t, none), (field, proof, none)])]
    cinfo := [("vehicle", {}), ("car", { parent := some "vehicle" }),
      ("bounded_box", {}), (family, { isIface := true })]
    sparams := [("bounded_box", [("t", false)]), (family, [("a", false), ("d", false)])]
    sbounds := [("bounded_box", [(vehicle, t)])]
    tvars := [("t", t), ("u", u)] }
  let input : SParam := { name := "B", ty := box.toSTy }
  let dictionary : SParam := { name := "D", ty := proof.toSTy }
  for params in [[input, dictionary], [dictionary, input]] do
    let (types, result) ← getOK "later/earlier actual dictionaries justify formal kinds"
      (resolveSignatureTypes env p params box.toSTy)
    need "signature keeps the precise constrained type" (types.length == 2 && result == box)
  refused "an ordinary declaration must state or carry its constraint"
    (resolveSignatureTypes env p [input] box.toSTy "F")
  refused "an overload rename does not confer helper privileges"
    (resolveSignatureTypes env p [input] box.toSTy "F$ov0")
  refused "type-value dictionaries cannot justify a kind"
    (resolveSignatureTypes env p [input, { dictionary with typeValue := true }] box.toSTy)
  refused "reversed dictionaries cannot justify a kind"
    (resolveSignatureTypes env p [input, { dictionary with ty := (Bound.mk t vehicle).ty.toSTy }] box.toSTy)
  refused "a compound relation cannot be distributed to its components"
    (resolveSignatureTypes env p [input, { dictionary with ty := (Bound.mk vehicle (.tup [t, u])).ty.toSTy }] box.toSTy)
  let _ ← getOK "a generated helper carries the actual object's readonly proof"
    (resolveSignatureTypes env p [input] box.toSTy "$contBounded")
  refused "a dummy object cannot provide its dictionary fields"
    (resolveSignatureTypes env p [{ input with typeValue := true }] box.toSTy "$contBounded")
  refused "a mutable field is not a stable helper proof"
    (resolveSignatureTypes { env with varFields := [("bounded_box", field)] } p [input] box.toSTy "$contBounded")
  let captured := [("$capture0", box, none)]
  let capturedFacts := fieldFacts env "$forStageExample" captured
  need "captured environments retain the complete relation" (capturedFacts == [(vehicle, t)])
  need "type-value environment fields contribute no facts"
    ((fieldFacts env "$forStageExample" [("$w.capture0", box, none)]).isEmpty)
  need "ordinary user object fields do not invent class constraints"
    ((fieldFacts env "ordinary_box" captured).isEmpty)
  need "mutable captures do not justify environment field kinds"
    ((fieldFacts { env with varFields := [("$forStageExample", "$capture0")] }
      "$forStageExample" captured).isEmpty)
  let signature : Sig := {
    idx := 0, name := "F", params := [box, proof], ret := box,
    decides := false, isConst := false, tparams := [("t", false)] }
  need "body scope includes actual explicit proof parameters"
    ((signature.typeEnv env).boundSubtype t vehicle)
  let ambient := { env with boundFacts := [(vehicle, t)] }
  let dummy := { signature with typeValues := [1] }
  let method := { signature with
    tparams := [("t", false), ("u", false)]
    bounds := [⟨vehicle, t⟩, ⟨.struct "car" [], u⟩] }
  need "override domains separate method constraints from receiver constraints"
    (method.methodBounds 1 == [⟨.struct "car" [], u⟩] && (method.methodBounds 2).isEmpty)
  need "body scope resets caller facts and excludes dummy parameters"
    (!(dummy.typeEnv ambient).boundSubtype t vehicle)
  refused "caller assumptions do not repair a dummy signature"
    (resolveSignatureTypes (dummy.typeEnv ambient) p
      [input, { dictionary with typeValue := true }] box.toSTy)
  let caller : Ctx := {
    sigs := [], sigProg := { fns := [], main := 0 }, types := env
    locals := [{ name := "Witness", slot := 0, ty := proof, mutable := false, typeValue := true }] }
  need "dummy local cannot authorize executable views"
    ((find? env caller.evidenceTypes ⟨vehicle, t⟩).isNone &&
      !(caller.evidenceEnv.boundSubtype t vehicle) && (caller.captureEvidence []).isEmpty)
  let outer : Local := { name := "Witness", slot := 1, ty := proof, mutable := false }
  let shadowed := { caller with locals := caller.locals ++ [outer] }
  need "excluding a dummy does not reveal a shadowed dictionary"
    ((find? env shadowed.evidenceTypes ⟨vehicle, t⟩).isNone)
  let (value, aliased) ← getOK "copy a renamed dummy value"
    ((elabStmt caller (.decl p "Alias" none false (.ident p "Witness")) none).run
      { env, nslots := 1, slotTys := #[proof] })
  need "aliases retain dummy provenance"
    ((value.2.lookup "Alias").any (·.typeValue) &&
      (find? env value.2.evidenceTypes ⟨vehicle, t⟩).isNone)
  need "aliasing retains an ordinary checked slot" (aliased.nslots == 2)
  let actual := { caller with locals :=
    [{ name := "$typeActualProof", slot := 0, ty := proof, mutable := false }] }
  let markedCaller := { actual with locals := actual.locals.map fun binding => { binding with typeValue := true } }
  let written := [SExpr.ident p "$typeActualProof"]
  need "first-success cache distinguishes a lexically used dummy from a proof"
    (firstKey actual p [] "B" none written != firstKey markedCaller p [] "B" none written)
  need "continuation cache distinguishes a lexically used dummy from a proof"
    (contKey actual p "B" written != contKey markedCaller p "B" written)
  let unused : Local := { name := "Unused", slot := 1, ty := proof, mutable := false, typeValue := true }
  let extra := { actual with locals := unused :: actual.locals }
  need "unused dummy names do not multiply continuation identities"
    (firstKey actual p [] "B" none written == firstKey extra p [] "B" none written)
  need "provenance is not guessed from a lexical name"
    ((find? env actual.evidenceTypes ⟨vehicle, t⟩).isSome)
  let formal : ResolvedTParams := { params := [("t", false)], bounds := [⟨vehicle, t⟩] }
  let _ ← getOK "inlined opaque calls use the caller's actual dictionary"
    (actual.checkInlineInstance p formal [("t", t)])
  let _ ← getOK "inlined nominal calls retain their precise instance"
    (actual.checkInlineInstance p formal [("t", .struct "car" [])])
  refused "inlining cannot erase an unused bound"
    (actual.checkInlineInstance p formal [("t", .int)])
  refused "inlining cannot promote a dummy dictionary"
    (caller.checkInlineInstance p formal [("t", t)])
  let aliases (value : SExpr) : List (String × SExpr) := [
    ("direct", value),
    ("final declaration", .block p [.decl p "Inner" none false value]),
    ("statement then final declaration", .block p [.int p 0, .decl p "Inner" none false value]),
    ("explicit inner result", .block p [.decl p "Inner" none false value, .ident p "Inner"]),
    ("case result", .caseE p (.int p 1) [(some (.int p 1), value), (none, value)]),
    ("case literal result", .caseE p (.int p 1) [(some (.int p 1), value), (none, .ident p "Other")]),
    ("case fallback result", .caseE p (.int p 1) [(some (.int p 1), .ident p "Other"), (none, value)]),
    ("conditional binding result", .ite p [.decl p "Inner" none false value, .query p (.ident p "true")]
      (.ident p "Inner") (some (.ident p "Other"))),
    ("queried option", .query p (.optionLit p value)),
    ("map lookup", .app p (.mapLit p [(.int p 1, value)]) [.int p 1] true),
    ("for body result", .app p (.forE p [.gen p "I" none (.arrayLit p [.int p 1])] value) [.int p 0] true),
    ("for bound result", .app p (.forE p [.gen p "Captured" none (.arrayLit p [value])]
      (.ident p "Captured")) [.int p 0] true),
    ("for later declaration", .app p (.forE p [.gen p "Captured" none (.arrayLit p [value]),
      .decl p "Saved" none false (.ident p "Captured")] (.ident p "Saved")) [.int p 0] true),
    ("for dependent generator", .app p (.forE p [.gen p "First" none (.arrayLit p [value]),
      .gen p "Second" none (.arrayLit p [.ident p "First"])] (.ident p "Second")) [.int p 0] true),
    ("map generator bound result", .app p (.forE p
      [.gen p "Captured" (some "Key") (.mapLit p [(.int p 1, value)])]
      (.ident p "Captured")) [.int p 0] true)]
  for dummyRole in [true, false] do
    let scope := { caller with
      canFail := true,
      locals := (caller.locals.map fun binding => { binding with typeValue := dummyRole }) ++
        [{ name := "Other", slot := 1, ty := proof, mutable := false }] }
    for (shape, rhs) in aliases (.ident p "Witness") do
      let (result, _) ← getOK s!"elaborate {shape} alias"
        ((elabStmt scope (.decl p "Leaked" none false rhs) none).run
          { env, nslots := 2, slotTys := #[proof, proof] })
      let aliasScope := { result.2 with locals := result.2.locals.filter (·.name == "Leaked") }
      need s!"{shape} preserves the returned value's dummy role"
        ((result.2.lookup "Leaked").any (·.typeValue) == dummyRole)
      need s!"{shape} cannot promote dummy evidence"
        ((find? env aliasScope.evidenceTypes ⟨vehicle, t⟩).isSome == !dummyRole)
      if dummyRole then
        refused s!"{shape} cannot authorize an inlined bound"
          (aliasScope.checkInlineInstance p formal [("t", t)])
      else
        discard <| getOK s!"{shape} retains usable real evidence"
          (aliasScope.checkInlineInstance p formal [("t", t)])
    let independent := SExpr.app p (.forE p
      [.gen p "Captured" none (.arrayLit p [.ident p "Witness"])] (.ident p "Other")) [.int p 0] true
    let (result, _) ← getOK "a generator can return an independent real proof"
      ((elabStmt scope (.decl p "Independent" none false independent) none).run
        { env, nslots := 2, slotTys := #[proof, proof] })
    let independentScope := { result.2 with locals := result.2.locals.filter (·.name == "Independent") }
    need "a dummy generator input does not taint an independent real result"
      (!(independentScope.lookup "Independent").any (·.typeValue) &&
        (find? env independentScope.evidenceTypes ⟨vehicle, t⟩).any (·.valid env independentScope.evidenceTypes))
  refused "inlining needs executable evidence even with a static fact"
    (({ caller with locals := [], types := ambient } : Ctx).checkInlineInstance p formal [("t", t)])
  let _ ← getOK "omitted defaults can complete an inlined instance later"
    (actual.checkInlineInstance p formal [] false)
  need "an inlined instance must be complete before use"
    ((actual.checkInlineInstance p formal []).toOption.isNone)
  let a := Ty.param "a" false
  let lower := Ty.param "lower" false
  let projected := { env with
    classes := env.classes ++ ["root", "leaf"]
    structs := env.structs ++ [("root", []), ("leaf", [])]
    cinfo := env.cinfo ++ [("root", {}), ("leaf", { parent := some "root" })]
    sparams := env.sparams ++ [("root", [("r", false)]), ("leaf", [("l", false)])]
    pargs := [("leaf", [.param "l" false])] }
  let projectedSig : Sig := {
    idx := 0, name := "Projected", params := [lower, .arr a], ret := .arr a,
    decides := false, isConst := false, fx := [], tparams := [("a", false), ("lower", false)],
    bounds := [⟨.struct "root" [a], lower⟩] }
  let leaf := Ty.struct "leaf" [.int]
  let projectedCaller : Ctx := {
    sigs := [projectedSig], sigProg := { fns := [], main := 0 }, types := projected
    locals := [{ name := "X", slot := 0, ty := leaf, mutable := false }] }
  for expected in [none, some (Ty.arr .any)] do
    let (result, _) ← getOK "nominal inference precedes contextual empties and can retry a wide result"
      ((elabGenericCallWith elabE projectedCaller p projectedSig
        [.ident p "X", .arrayLit p []] expected).run { env := projected, nslots := 1, slotTys := #[leaf] })
    need "a partial result context cannot replace the valid projected instance" (result.ty == .arr .int)
  let car := Ty.struct "car" []
  let truck := Ty.struct "truck" []
  let left := Ty.struct "left" []
  let right := Ty.struct "right" []
  let domains := { projected with
    classes := projected.classes ++ ["truck", "left", "right"]
    cinfo := projected.cinfo ++ [("truck", { parent := some "vehicle" }),
      ("left", { isIface := true }), ("right", { isIface := true })] }
  let cars := [(car, t)]
  let trucks := [(truck, t)]
  need "same-spelled overload formals have independent sibling bounds"
    (domains.paramsDistinct [t] [t] cars trucks && domains.paramsDistinct [t] [t] trucks cars)
  need "an ancestor bound still overlaps its descendant"
    (!(domains.paramsDistinct [t] [u] cars [(vehicle, u)]))
  need "uninhabited unrelated interfaces can have a common subtype"
    (!(domains.paramsDistinct [t] [t] [(left, t)] [(right, t)]))
  need "a forward peer chain carries its separating class bound"
    (domains.paramsDistinct [t] [t] [(u, t), (car, u)] trucks)
  need "a peer cycle is not evidence of domain separation"
    (!(domains.paramsDistinct [t] [t] [(u, t), (t, u)] trucks))
  need "any valid upper view can separate an intersection"
    (domains.paramsDistinct [t] [t] [(left, t), (car, t)] trucks &&
      domains.paramsDistinct [t] [t] [(car, t), (left, t)] trucks)
  need "projected generic bounds retain their invariant arguments"
    (domains.paramsDistinct [t] [t]
      [(.struct "root" [.int], t)] [(.struct "root" [Ty.string], t)])
  need "empty arrays still overlap despite disjoint element bounds"
    (!(domains.paramsDistinct [.arr t] [.arr t] cars trucks))
  need "flattening tuples retains the respective formal scopes"
    (domains.paramsDistinct [.tup [t, .int]] [t, .int] cars trucks &&
      domains.paramsDistinct [t, .int] [.tup [t, .int]] trucks cars)
  need "tuple adaptation does not separate the same bounded domain"
    (!(domains.paramsDistinct [.tup [t, .int]] [t, .int] cars cars))
  need "tuple/map key comparison uses the map's own bound in either order"
    (domains.disjointUnder [(.int, t)] cars (.tup [t]) (.map t .int) &&
      domains.disjointUnder cars [(.int, t)] (.map t .int) (.tup [t]) &&
      !(domains.disjointUnder cars [(.int, t)] (.tup [t]) (.map t .int)))
  need "required named bounds can distinguish sibling overloads"
    (domains.namedDistinct [("X", false, t)] [("X", false, t)] cars trucks)
  need "omitting optional parameters still fits both overloads"
    (!(domains.namedDistinct [("X", true, t)] [("X", true, t)] cars trucks))
  let generic := { projectedSig with
    params := [t], ret := .int,
    tparams := [("t", false)], bounds := [⟨car, t⟩] }
  let valueType (input : Ty) := Ty.struct (FnValues.shapeOf 1 ["computes"]).name [input, .int]
  need "function-value overload matching checks the selected bound"
    (fnValueArgs domains generic (valueType car) == some [car] &&
      (fnValueArgs domains generic (valueType truck)).isNone)
  let parsed ← getOK "parse witness metadata fixture"
    (parseProgram "Echo(D:t where t:type):t=D|D\nMain():void=for(V:=Echo(7)){Print(\"{V}\")}")
  let marked := parsed.map fun
    | .fn p "Echo" ps tps specs ret body =>
      STop.fn p "Echo" (ps.map fun param => { param with typeValue := true }) tps specs ret body
    | top => top
  let (lowered, _) ← getOK "inline witness metadata" (Choice.inlineMulti marked [])
  need "inlining preserves a dummy value's role across renamed bindings"
    (lowered.any fun
      | .fn _ "Main" _ _ _ _ body => Choice.anyE (fun
          | .app _ (.ident _ "$typeValue") [_] false => true
          | _ => false) body
      | _ => false)
  let bounded := TParam.withUpperBound p "t" (.name "vehicle")
  let adapters := FnValues.genericAdapters p "Bounded" [.name "t"] [bounded] (.name "t") [1, 2]
  need "nominal bounds exclude impossible tuple value classes"
    (!adapters.any (·.suffix.startsWith "Unpack"))
  let peer := TParam.withUpperBound p "u" (.name "t")
  let peers := FnValues.genericAdapters p "PeerBounded" [.name "u"] [peer, bounded] (.name "u") [1, 2]
  need "a nominal exclusion follows a forward peer chain"
    (!peers.any (·.suffix.startsWith "Unpack"))
  let comparable : TParam := { pos := p, name := "t", constraint := "comparable" }
  let tuples := FnValues.genericAdapters p "Comparable" [.name "t"] [comparable] (.name "t") [2]
  need "comparable tuple adapters retain component comparability"
    (tuples.any fun adapter => adapter.suffix == "Unpack2" &&
      adapter.tparams.all (fun tp => tp.constraint == "comparable" && tp.upperBound.isNone))
  let plain : TParam := { pos := p, name := "t", constraint := "type" }
  let peers := FnValues.genericAdapters p "Split" [.name "u"] [plain, peer] (.name "u") [2]
  let some unpack := peers.find? (·.suffix == "Unpack2")
    | throw (IO.userError "peer tuple adapter lost its bound-only parameter")
  need "tuple adapters retain the complete relation without distributing it"
    (reprStr unpack.relations == reprStr [(STy.name "t", STy.tup unpack.params)] &&
      unpack.tparams.length == 3 && unpack.tparams.any (·.name == "t") &&
      unpack.tparams.all (·.upperBound.isNone))
  let peers := FnValues.genericAdapters p "ComparablePeer" [.name "u"] [peer, comparable] (.name "u") [2]
  need "peer comparability reaches each tuple component"
    (peers.any fun adapter => adapter.suffix == "Unpack2" &&
      adapter.tparams.all (·.constraint == "comparable") && adapter.relations.length == 1)
  let lower : TParam := { pos := p, name := "u", constraint := "type" }
  need "a known upper does not infer an absent lower"
    (!(FnValues.boundInferredNames [plain, lower] [.name "t"] [(.name "t", .name "u")]).contains "u")
  let floating := TParam.withUpperBound p "v" (.name "v")
  let peers := FnValues.genericAdapters p "Phantom" [.name "u"] [plain, peer, floating] (.name "u") [2]
  need "an unreachable bound cycle does not create an unusable tuple class"
    (!peers.any (·.suffix.startsWith "Unpack"))
  let capturedBound := TParam.withUpperBound p "v" (.name "vehicle")
  let peers := FnValues.genericAdapters p "Captured" [.name "u"] [capturedBound, plain, peer]
    (.name "u") [2] [.app "holder" [.name "v"]]
  need "retained receiver bounds keep their nominal comparability information"
    (peers.any fun adapter => adapter.suffix == "Unpack2" && adapter.relations.length == 1 &&
      adapter.tparams.any (fun tp => tp.name == "v" && reprStr tp.upperBound == reprStr capturedBound.upperBound))
  let source := "vehicle:=class<computes>{Speed:int=9}\nF(X:t,D:evidence(vehicle,t) where t:type)<computes>:int=X.Speed\nMain():void={}"
  let parsed ← getOK "parse role-controlled dictionary parameters" (parseProgram source)
  let roles (tops : List STop) (typeValue : Bool) : IO (List STop) := tops.mapM fun
    | .fn p name ps tps specs ret body => do
      let ps ← ps.mapM fun param => do
        let ty ← getOK "resolve private protocol spelling"
          (param.ty.mapNamesM fun name => pure (if name == "evidence" then family else name))
        pure { param with ty, typeValue := typeValue && param.name == "D" }
      pure (.fn p name ps tps specs ret body)
    | top => pure top
  let actual ← roles parsed false
  let compiled ← getOK "real dictionary body checks" (elabProgram actual)
  need "real dictionary body passes Core typing"
    (compiled.prog.check && compiled.prog.checkTypes compiled.sigs compiled.slotTys && compiled.prog.checkControl)
  let dummy ← roles parsed true
  match elabProgram dummy with
  | .error message => need "dummy body has no executable bound view" ((message.splitOn "has no member").length > 1)
  | .ok _ => throw (IO.userError "a dummy parameter became executable subtype evidence")
  let interior := "vehicle:=class<allocates>{var N:int=0}\nbox(t:type):=class<computes>{X:t}\nF(B:box(t),D:evidence(vehicle,t) where t:type)<transacts>:void=set B.X.N=1\nMain():void={}"
  let parsed ← getOK "parse role-controlled interior path" (parseProgram interior)
  let actual ← roles parsed false
  let compiled ← getOK "real evidence admits an interior path" (elabProgram actual)
  need "interior path passes ordinary Core typing"
    (compiled.prog.check && compiled.prog.checkControl && compiled.prog.checkTypes compiled.sigs compiled.slotTys)
  let dummy ← roles parsed true
  match elabProgram dummy with
  | .error message =>
    need "an interior path cannot promote a dummy dictionary" ((message.splitOn "has no field").length > 1)
  | .ok _ => throw (IO.userError "an interior path wrote through a dummy dictionary")
  IO.println "subtype evidence scope contracts passed (formal kinds, real captures, dummy provenance, aliasing and inlining)"
