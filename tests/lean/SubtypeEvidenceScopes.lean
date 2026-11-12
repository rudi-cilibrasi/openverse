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
  let source := "vehicle:=class<computes>{Speed:int=9}\nF(X:t,D:evidence(vehicle,t) where t:type)<computes>:int=X.Speed\nMain():void={}"
  let parsed ← getOK "parse role-controlled dictionary parameters" (parseProgram source)
  let roles (typeValue : Bool) : IO (List STop) := parsed.mapM fun
    | .fn p name ps tps specs ret body => do
      let ps ← ps.mapM fun param => do
        let ty ← getOK "resolve private protocol spelling"
          (param.ty.mapNamesM fun name => pure (if name == "evidence" then family else name))
        pure { param with ty, typeValue := typeValue && param.name == "D" }
      pure (.fn p name ps tps specs ret body)
    | top => pure top
  let actual ← roles false
  let compiled ← getOK "real dictionary body checks" (elabProgram actual)
  need "real dictionary body passes Core typing"
    (compiled.prog.check && compiled.prog.checkTypes compiled.sigs compiled.slotTys && compiled.prog.checkControl)
  let dummy ← roles true
  match elabProgram dummy with
  | .error message => need "dummy body has no executable bound view" ((message.splitOn "has no member").length > 1)
  | .ok _ => throw (IO.userError "a dummy parameter became executable subtype evidence")
  IO.println "subtype evidence scope contracts passed (formal kinds, real captures, dummy provenance, aliasing and inlining)"
