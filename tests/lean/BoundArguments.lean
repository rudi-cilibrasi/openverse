import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front OpenVerse.Front.SubtypeEvidence

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def t : Ty := .param "t" false
private def a : Ty := .param "a" false
private def car : Ty := .struct "car" []
private def truck : Ty := .struct "truck" []
private def box (ty : Ty) : Ty := .struct "box" [ty]
private def types : TyEnv := {
  classes := ["box", "leaf", "car", "truck"]
  structs := [("box", []), ("leaf", []), ("car", []), ("truck", [])]
  cinfo := [("box", {}), ("leaf", { parent := some "box" }), ("car", {}), ("truck", {})]
  sparams := [("box", [("item", false)]), ("leaf", [("item", false)])]
  pargs := [("leaf", [.param "item" false])]
  tvars := [("t", t)] }

private def proof (name : String) (upper : Ty) (dummy : Bool := false) : Local := {
  name, slot := 3, ty := (Bound.mk upper t).ty, mutable := false, typeValue := dummy }
private def context (locals : List Local) : Ctx := {
  sigs := [], sigProg := { fns := [], main := 0 }
  types := { types with boundFacts := [(box car, t)] }, locals }

def main : IO Unit := do
  let actual := context [proof "D" (box car)]
  need "real nominal view infers the application argument"
    ((actual.matchArgument [] (box a) t).any fun result => result.lookup "a" == some car)
  for ctx in [context [], context [proof "D" (box car) true]] do
    need "facts or dummy capabilities do not infer a nominal view"
      ((ctx.matchArgument [] (box a) t).isNone)
  need "direct opaque parameter matching preserves its precise type"
    ((actual.matchArgument [] (.param "u" false) t).any fun result => result.lookup "u" == some t)
  need "nested container patterns use actual component views"
    ((actual.matchArgument [] (.arr (box a)) (.arr t)).any fun result => result.lookup "a" == some car)
  for locals in [[proof "Box" (box car), proof "Leaf" (.struct "leaf" [car])],
      [proof "Leaf" (.struct "leaf" [car]), proof "Box" (box car)]] do
    need "agreeing projected views infer the same instance in either order"
      (((context locals).matchArgument [] (box a) t).any fun result => result.lookup "a" == some car)
  for locals in [[proof "Car" (box car), proof "Truck" (box truck)],
      [proof "Truck" (box truck), proof "Car" (box car)]] do
    need "distinct inferred applications remain ambiguous"
      (((context locals).matchArgument [] (box a) t).isNone)
  need "a fixed application argument is retained"
    ((actual.matchArgument [("a", car)] (box a) t).isSome)
  need "a fixed incompatible application is refused"
    ((actual.matchArgument [("a", truck)] (box a) t).isNone)
  IO.println "bound argument contracts passed (actual views, nested patterns, precise inputs and instance agreement)"
