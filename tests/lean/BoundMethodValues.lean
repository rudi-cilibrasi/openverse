import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front OpenVerse.Front.SubtypeEvidence

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def require (label : String) (result : Except String (Option α)) : IO α := do
  match result with
  | .ok (some value) => pure value
  | .ok none => throw (IO.userError s!"{label}: no adapter")
  | .error message => throw (IO.userError s!"{label}: {message}")

private def p : Pos := { line := 1, col := 1 }
private def vehicle : Ty := .struct "vehicle" []
private def reader : Ty := .struct "reader" []
private def t : Ty := .param "t" false
private def fn (params : List Ty) (ret : Ty) : Ty :=
  .struct (FnValues.shapeOf params.length ["computes"]).name (params ++ [ret])
private def types : TyEnv := {
  classes := ["vehicle", "car", "reader", "box", "holder"]
  structs := [("vehicle", []), ("car", []), ("reader", []), ("box", []), ("holder", [])]
  cinfo := [("vehicle", {}), ("car", { parent := some "vehicle" }), ("reader", {}), ("box", {}), ("holder", {})]
  sparams := [("box", [("a", false)]), ("holder", [("a", false)])]
  sbounds := [("box", [(vehicle, .param "a" false)])]
  tvars := [("t", t)] }

private def context (name : String := "t") (dummy : Bool := false) (keep : Bool := true) : Ctx := {
  sigs := [], sigProg := { fns := [], main := 0 }
  types := { types with tvars := [(name, .param name false)], boundFacts := [(vehicle, .param name false)] }
  locals := if keep then [{
    name := "Proof", slot := 4, ty := (Bound.mk vehicle (.param name false)).ty
    mutable := false, typeValue := dummy }] else [] }

private def request (ctx : Ctx) (receiver own target : Ty) :=
  (methodVarianceRequest ctx p "reader" "Read" receiver own target).run' { env := ctx.types }

def main : IO Unit := do
  let own := fn [vehicle] vehicle
  let target := fn [t] vehicle
  let (argument, args) ← require "contravariant bounded argument" (request (context) reader own target)
  let privateT := STy.name "$methodVariance0"
  need "argument adapter retains its actual instance" (args == [t])
  need "argument adapter retains its whole relation"
    (reprStr argument.relations == reprStr [(STy.name "vehicle", privateT)])
  for ctx in [context "t" true, context "t" false false] do
    need "dummy or static facts cannot justify an argument adapter"
      (match request ctx reader own target with | .ok none => true | _ => false)
  let renamed := Ty.param "renamed" false
  let (alpha, _) ← require "renamed proof" (request (context "renamed") reader own (fn [renamed] vehicle))
  need "adapter keys do not retain caller type-variable names" (alpha.key == argument.key)
  let (result, _) ← require "covariant bounded result"
    (request (context) (.struct "box" [t]) (fn [] t) (fn [] vehicle))
  need "result and receiver application share a single retained relation" (result.relations.length == 1)
  let (application, _) ← require "bounded receiver with ordinary conversions"
    (request (context) (.struct "box" [t]) own (fn [.struct "car" []] vehicle))
  need "receiver application constraints survive ordinary conversions" (application.relations.length == 1)
  need "receiver constraints require real evidence"
    (match request (context "t" false false) (.struct "box" [t]) own (fn [.struct "car" []] vehicle) with
      | .ok none => true | _ => false)
  let lower := Ty.tup [t, .int]
  let upper := Ty.param "upper" false
  let whole := Bound.mk upper lower
  let ctx := { context with
    types := { types with tvars := [("t", t), ("upper", upper)], boundFacts := [(upper, lower)] }
    locals := [{ name := "Whole", slot := 7, ty := whole.ty, mutable := false }] }
  let (packed, _) ← require "whole-tuple argument adapter"
    (request ctx (.struct "holder" [upper]) (fn [upper] .int) (fn [t, .int] .int))
  need "whole-tuple proof is retained without component assumptions"
    (packed.relations.length == 1 && packed.relations.any fun (_, lower) => match lower with
      | .tup [_, .name "int"] => true | _ => false)
  let generated := FnValues.desugar [] [] [] [argument]
  let fields := generated.findSome? fun
    | .classDef _ name _ _ _ _ _ fields _ =>
      if name == argument.className 0 then some fields else none
    | _ => none
  need "generated adapter stores a readonly real relation field"
    (fields.any fun fields => fields.any fun ⟨name, ty, _, mutable, _, _⟩ =>
      (SubtypeEvidence.declaredRelation? (argument.className 0) name ty mutable).isSome)
  need "upper-bound evidence does not justify reverse narrowing"
    (match request (context) reader (fn [t] vehicle) (fn [vehicle] vehicle) with
      | .ok none => true | _ => false)
  IO.println "bound method-value contracts passed (variance, actual evidence, whole relations and canonical capture)"
