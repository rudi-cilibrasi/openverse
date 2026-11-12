import OpenVerse.Front.Elab
import OpenVerse.Front.SubtypeEvidence
import OpenVerse.Core.Bounded
import OpenVerse.Core.Encode

open OpenVerse OpenVerse.Front
open OpenVerse.Front.SubtypeEvidence

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

private def env : TyEnv := {
  classes := ["vehicle", "car", "node", "left", "right", "both"]
  cinfo := [("vehicle", {}), ("car", { parent := some "vehicle" }),
    ("node", { parent := some "vehicle" }), ("left", { isIface := true }),
    ("right", { isIface := true }), ("both", { ifaces := ["left", "right"] })]
  sparams := [("node", [("t", false)])] }

private def pos : Pos := { line := 1, col := 1, file := "subtype-evidence.verse" }

private def rewrite (replacements : List (String × SExpr)) (body : SExpr) : Except String SExpr := do
  let rename (name : String) := if name == "evidence" then family else name
  let r : Resolver := {
    val := fun _ name => pure (rename name), ty := fun _ name => pure (rename name),
    bind := fun _ _ => pure (), qual := fun _ _ => pure none }
  let body := Choice.mapE (fun
    | .app _ (.ident _ name) [] false => replacements.lookup name
    | _ => none) body
  body.mapNamesM r

private partial def rewriteTop (replacements : List (String × SExpr)) : STop → Except String STop
  | .fn p name ps tps specs ret body => do
    let rename (name : String) : Except String String := pure (if name == "evidence" then family else name)
    let ps ← ps.mapM fun param => do
      let ty ← param.ty.mapNamesM rename
      let value ← param.default.mapM (rewrite replacements)
      return { param with ty, default := value }
    return .fn p name ps tps specs (← ret.mapNamesM rename) (← rewrite replacements body)
  | .classDef p name tps specs parents iface fields overrides methods => do
    let rename (name : String) : Except String String := pure (if name == "evidence" then family else name)
    let fields ← fields.mapM fun (name, ty, value, mutable) => do
      return (name, ← ty.mapNamesM rename, ← value.mapM (rewrite replacements), mutable)
    return .classDef p name tps specs (← parents.mapM (·.mapNamesM rename)) iface fields overrides
      (← methods.mapM (rewriteTop replacements))
  | .const p name ty body => return .const p name ty (← rewrite replacements body)

private def source := "
vehicle:=class<computes>{Speed:int=1}
car:=class<computes>(vehicle){Name:string=\"car\"}
node(t:type):=class<computes>(vehicle){Value:t}
box(t:type):=class<computes>{Value:t}
Process(X:t,D:evidence(vehicle,t) where t:type)<computes>:t=
    Print(\"speed {D.Up(X).Speed}\")
    X
UseBox(B:box(t),D:evidence(vehicle,t) where t:type)<computes>:t=Process(B.Value,D)
closure(t:type):=class<computes>:
    B:box(t)
    D:evidence(vehicle,t)
    Run()<computes>:t=UseBox(B,D)
Bind(B:box(t),D:evidence(vehicle,t) where t:type)<computes>:type{_()<computes>:t}=
    closure(t){B:=B,D:=D}.Run
Walk(X:t,D:evidence(vehicle,t),N:int where t:type)<computes>:int=
    if(N>0):
        Y:=node(t){Value:=X,Speed:=N}
        return Walk(Y,NodeEvidence(),N-1)
    D.Up(X).Speed
Widen(Base:t,Derived:u,D:evidence(t,u) where t:type,u:type)<computes>:t=D.Up(Derived)
Main():void=
    C:=car{Speed:=9,Name:=\"precise\"}
    R:=Process(C,CarEvidence())
    Print(\"name {R.Name}\")
    F:=Bind(box(car){Value:=C},CarEvidence())
    Print(\"escape {F().Name}\")
    Print(\"poly {Walk(C,CarEvidence(),3)}\")
    Print(\"composed {Widen(vehicle{},C,ComposedEvidence()).Speed}\")
    Print(\"identity {Widen(1,7,IntEvidence())}\")
"

private def trace := "speed 9\nname precise\nspeed 9\nescape precise\npoly 1\ncomposed 9\nidentity 7\n"

def main (args : List String) : IO Unit := do
  let vehicle := Ty.struct "vehicle" []
  let car := Ty.struct "car" []
  let node := Ty.struct "node" [.int]
  let t := Ty.param "t" false
  let u := Ty.param "u" false
  let v := Ty.param "v" false
  let carPlan ← getSome "missing nominal upcast" (find? env [] ⟨vehicle, car⟩)
  need "nominal plan validation" (carPlan.valid env [])
  need "wrong generic projection refused" ((find? env [] ⟨.struct "node" [Ty.string], node⟩).isNone)
  need "unrelated interfaces are not evidence" ((find? env [] ⟨.struct "left" [], .struct "right" []⟩).isNone)
  need "interface overlap remains possible" ((find? env [] ⟨.struct "left" [], .struct "both" []⟩).isSome &&
    (find? env [] ⟨.struct "right" [], .struct "both" []⟩).isSome)
  let locals := [("TU", (Bound.mk t u).ty), ("UV", (Bound.mk u v).ty)]
  let dependent ← getSome "missing transitive relation" (find? env locals ⟨t, v⟩)
  need "dependent plan validation" (dependent.valid env locals && dependent.bound env == ⟨t, v⟩)
  need "missing capture refused" (!dependent.valid env locals.tail)
  need "same-name unrelated capture refused" (!dependent.valid env [("TU", .int), ("UV", (Bound.mk u v).ty)])
  need "reverse relation refused" ((find? env locals ⟨v, t⟩).isNone)
  let cycles := [("UT", (Bound.mk u t).ty), ("TU", (Bound.mk t u).ty)]
  need "cycles terminate" ((find? env cycles ⟨v, t⟩).isNone)
  let cycleExit := cycles ++ [("TV", (Bound.mk v t).ty)]
  need "cycle does not hide later path" ((find? env cycleExit ⟨v, u⟩).isSome)
  let nominalPrefix := [("TVehicle", (Bound.mk t vehicle).ty)]
  let projected ← getSome "missing nominal/dependent composition" (find? env nominalPrefix ⟨t, car⟩)
  need "nominal/dependent composition validates" (projected.valid env nominalPrefix)
  need "compound constraint survives substitution"
    ((Bound.mk vehicle t).subst [("t", .tup [.int, .logic])] == ⟨vehicle, .tup [.int, .logic]⟩)
  let combined := Plan.compose carPlan (.identity car)
  need "one family across closed instances" ((Plan.compose
    (.nominal "node" "vehicle" [.int]) (.identity node)).nominals ==
    (Plan.nominal "node" "vehicle" [Ty.string]).nominals)
  need "ill-typed composition refused" (!(Plan.compose carPlan (.identity .int)).valid env [])
  let replacements := [
    ("CarEvidence", carPlan.value env pos),
    ("NodeEvidence", (Plan.nominal "node" "vehicle" [t]).value env pos),
    ("ComposedEvidence", combined.value env pos),
    ("IntEvidence", (Plan.identity .int).value env pos)]
  let tops ← getOK "parse dictionary control" (parseProgram source)
  let tops ← getOK "resolve dictionary controls" (tops.mapM (rewriteTop replacements))
  let nominals ← getOK "generate canonical nominal families"
    ([ ("car", "vehicle"), ("node", "vehicle") ].mapM fun (source, target) => nominal env pos source target)
  let compiled ← getOK "checked dictionaries" (elabProgram (protocol pos ++ nominals ++ tops))
  need "Core admission" (compiled.prog.check && compiled.prog.checkControl &&
    compiled.prog.checkTypes compiled.sigs compiled.slotTys)
  match compiled.prog.runB 1000000 10000 with
  | .res (.ok _, output) =>
    need "independent dictionary trace" (ByteArray.mk (output.map Nat.toUInt8).toArray == trace.toUTF8)
  | other => throw (IO.userError s!"dictionary execution failed: {reprStr other}")
  -- Even a malformed compiler-supplied plan cannot bypass ordinary Core
  -- typing. This calls the real generated Up method at incompatible types.
  let bad := (Plan.compose carPlan (.identity .int)).value env pos
  let badMain := STop.fn pos "Main" [] [] [] (.name "void") bad
  let declarations := tops.filter fun | .fn _ "Main" .. => false | _ => true
  match elabProgram (protocol pos ++ nominals ++ declarations ++ [badMain]) with
  | .error message =>
    need "wrong composition reaches a type diagnostic" ((message.splitOn "expected").length > 1)
  | .ok _ => throw (IO.userError "ill-typed dictionary composition passed the compiler")
  if let [out] := args then
    IO.FS.writeBinFile (out ++ "/evidence.vbc") compiled.prog.encode
    IO.FS.writeFile (out ++ "/evidence.expected") trace
  IO.println "subtype dictionary contracts passed (checked Core, precise/escaping results, polymorphic recursion, dependent composition)"
