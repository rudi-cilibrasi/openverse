import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front OpenVerse.Front.SubtypeEvidence

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def getOK (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{label}: {message}")

private def getSome (label : String) (result : Option α) : IO α :=
  match result with
  | some value => pure value
  | none => throw (IO.userError label)

private def p : Pos := { line := 1, col := 1 }
private def row : Ty := .param "row" false
private def t : Ty := .param "t" false
private def vehicle : Ty := .struct "vehicle" []
private def types : TyEnv := {
  classes := ["vehicle", "car", "ca", "cb", "root"]
  structs := [("vehicle", []), ("car", []), ("ca", []), ("cb", []), ("root", [])]
  cinfo := [("vehicle", {}), ("car", { parent := some "vehicle" }), ("ca", {}), ("cb", {}), ("root", {})]
  sparams := [("root", [("a", false)])]
  tvars := [("row", row), ("t", t)] }

private def call : SExpr := .app p (.member p (.ident p "Row") "Apply") [.ident p "X"] false

private def operation (vars : List (String × Bool)) (bounds : List Bound) : Option ChoiceOperations :=
  let input := Ty.param (vars.getLast!.1) false
  let plan : ChoiceTypes.Plan := {
    binding := row, params := [("row", false)],
    instances := [[("row", .struct "ca" [])], [("row", .struct "cb" [])]] }
  let cases := ["ca", "cb"].map fun name => ({
    receiver := .struct name [], inputs := [input], result := .int, specs := ["computes"],
    methodVars := vars, methodBounds := bounds, omittedDefaults := true } : ChoiceOperationCase)
  choiceGenericOperation { sigs := [], sigProg := { fns := [], main := 0 }, types }
    "$testOperation" (.ident p "Row") row { plan } call cases

private partial def methodParams : STop → List (List TParam)
  | .fn _ _ _ tps .. => [tps]
  | .classDef _ _ _ _ _ _ _ _ methods => methods.flatMap methodParams
  | _ => []

private def classOperation (upper : Ty) : Option ChoiceOperations :=
  let a := Ty.param "a" false
  let u := Ty.param "$operationMethod0" false
  let extra := upper.params.eraseDups
  let args := t :: extra.map (fun name => Ty.param name false)
  let parameters := ("a", false) :: extra.map (·, false)
  let env := { types with
    sparams := types.sparams ++ [("ca", parameters), ("cb", parameters)]
    sbounds := [("ca", [(upper, a)]), ("cb", [(upper, a)])]
    tvars := types.tvars ++ extra.map (fun name => (name, Ty.param name false)) }
  let plan : ChoiceTypes.Plan := {
    binding := row, params := [("row", false)],
    instances := [[("row", .struct "ca" args)], [("row", .struct "cb" args)]] }
  let cases := ["ca", "cb"].map fun name => ({
    receiver := .struct name args, inputs := [u], result := .int, specs := ["computes"],
    methodVars := [("$operationMethod0", false)], methodBounds := [⟨t, u⟩] } : ChoiceOperationCase)
  choiceGenericOperation { sigs := [], sigProg := { fns := [], main := 0 }, types := env }
    "$testClassOperation" (.ident p "Row") row { plan } call cases

private def declarationParams : STop → List TParam
  | .fn _ _ _ tps .. | .classDef _ _ tps .. => tps
  | _ => []

private def familyName (ops : ChoiceOperations) : Option String := do
  let (_, .struct name _) ← ops.params.head? | none
  return name

private def probe (ops : ChoiceOperations) (base : Ty) (dummy : Bool) (keep : Bool := true) : Except String R := do
  let (name, dictionary) ← match ops.params.head? with
    | some value => pure value
    | none => .error "missing operation dictionary"
  let proof := (Bound.mk base t).ty
  let ctx : Ctx := {
    sigs := [], sigProg := { fns := [], main := 0 }, typeOnly := true,
    types := { types with boundFacts := [(base, t)] },
    locals := [{ name := "X", slot := 0, ty := t, mutable := false },
      { name := "Row", slot := 2, ty := row, mutable := false },
      { name, slot := 3, ty := dictionary, mutable := false }] ++
      (if keep then [{ name := "D", slot := 1, ty := proof, mutable := false, typeValue := dummy }] else []) }
  let (result, _) ← (elabE ctx (ops.rewrite call) (some .int)).run
    { env := ctx.types, nslots := 4, slotTys := #[t, proof, row, dictionary] }
  return result

def main : IO Unit := do
  let u := Ty.param "$operationMethod0" false
  let bound := Bound.mk vehicle u
  let ops ← getSome "bounded method operation must remain representable" (operation [("$operationMethod0", false)] [bound])
  let declarations := ops.extraFns.flatMap methodParams
  need "interface, forwarding function and every implementation declare the upper bound"
    (declarations.length == 4 && declarations.all fun params => params.any fun param =>
      param.name == "$operationMethod0" && param.upperBound == some (.name "vehicle"))
  let result ← getOK "actual proof admits the typed generic operation" (probe ops vehicle false)
  need "bounded probe retains its result type" (result.ty == .int)
  for result in [probe ops vehicle true, probe ops vehicle false false] do
    match result with
    | .ok _ => throw (IO.userError "dummy/missing proof admitted a bounded operation")
    | .error message =>
      need "static facts cannot replace actual operation evidence"
        ((message.splitOn "does not satisfy subtype(vehicle)").length > 1)
  let plain ← getSome "ordinary generic operation" (operation [("$operationMethod0", false)] [])
  need "operation identity distinguishes a bounded method domain" (plain.params.head?.map (·.2) != ops.params.head?.map (·.2))
  let a := Ty.param "$operationMethod0" false
  let v := Ty.param "$operationMethod1" false
  let projected ← getSome "bound-only method parameter operation"
    (operation [("$operationMethod0", false), ("$operationMethod1", false)] [⟨.struct "root" [a], v⟩])
  let result ← getOK "probe infers a parameter occurring only in its bound"
    (probe projected (.struct "root" [.int]) false)
  need "bound-only inference returns the declared result" (result.ty == .int)
  need "a compound relation cannot be silently erased to a bare parameter"
    ((choiceMethodTParams p [("$operationMethod0", false)] [⟨vehicle, .tup [u, u]⟩]).isNone)
  let classes ← getSome "class-bound operations remain representable" (classOperation vehicle)
  need "interface, forwarder and implementations retain the required class bound"
    (classes.extraFns.length == 4 && classes.extraFns.all fun declaration =>
      (declarationParams declaration).any (·.upperBound == some (.name "vehicle")))
  let stricter ← getSome "a stricter class-bound operation" (classOperation (.struct "car" []))
  need "class bounds participate in operation identity" (familyName classes != familyName stricter)
  let dependent ← getSome "class bound-only dependencies remain representable"
    (classOperation (.struct "root" [.param "element" false]))
  need "class bound-only dependencies belong to the dictionary"
    (dependent.params.head?.any fun (_, ty) => match ty with
      | .struct _ args => args.length == 3 && args.any (· == .param "element" false)
      | _ => false)
  for declaration in dependent.extraFns do
    let params := declarationParams declaration
    need "renamed class bounds keep their own bound-only binder" (params.any fun tp => match tp.upperBound with
      | some (.app "root" [.name element]) => params.any (·.name == element)
      | _ => false)
  let renamed ← getSome "alpha-renamed class dependency"
    (classOperation (.struct "root" [.param "renamed" false]))
  need "class-bound identity ignores lexical dependency spellings" (familyName dependent == familyName renamed)
  let proof := (Bound.mk vehicle t).ty
  let proofField := fieldName "carrier" "t"
  let stage : Choice.ForStagePlan := {
    key := "bound-capture", pos := p, base := "$testStage", method := "$resume",
    tparams := [{ pos := p, name := "t", constraint := "type" }], value := .name "int",
    specs := ["suspends"], copies := [], borrowed := [] }
  for (dummy, mutableProof) in [(false, false), (true, false), (false, true)] do
    let env := { types with
      classes := "carrier" :: types.classes,
      structs := ("carrier", [(proofField, proof, none)]) :: types.structs,
      sparams := ("carrier", [("t", false)]) :: types.sparams,
      varFields := if mutableProof then [("carrier", proofField)] else [],
      boundFacts := [(vehicle, t)] }
    let ctx : Ctx := {
      sigs := [], sigProg := { fns := [], main := 0 }, types := env,
      forStageArgs := [t],
      locals := [{ name := "Carrier", slot := 0, ty := .struct "carrier" [t], mutable := false, typeValue := dummy }] }
    let (request, _, _) ← getOK "retain actual captured relations before local initialization"
      (forStageEnvOf ctx stage p [] (.block p [.ident p "Carrier", .int p 0]))
    let relations := request.extraFns.flatMap fun
      | .classDef _ owner _ _ _ _ fields _ _ => fields.filterMap fun (name, ty, _, mutable) =>
          declaredRelation? owner name ty mutable
      | _ => []
    need "resume fields preserve only actual readonly proof capabilities"
      (relations.length == (if dummy || mutableProof then 0 else 1))
  IO.println "choice bound-method contracts passed (class/method domains, real evidence, bound-only inference and cache identity)"
