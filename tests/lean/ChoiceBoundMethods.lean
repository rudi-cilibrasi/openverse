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
  IO.println "choice bound-method contracts passed (declared domains, real evidence, bound-only inference and cache identity)"
