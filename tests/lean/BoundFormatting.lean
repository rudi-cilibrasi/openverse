import OpenVerse.Front.Elab
import OpenVerse.Core.Bounded
import OpenVerse.Core.Encode

open OpenVerse OpenVerse.Front OpenVerse.Front.SubtypeEvidence

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)
private def getOK (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{label}: {message}")

private def p : Pos := { line := 1, col := 1 }
private def t : Ty := .param "t" false
private def a : Ty := .param "a" false
private def types : TyEnv := {
  tvars := [("t", t), ("a", a)]
  boundFacts := [(.int, t), (.char, a)]
  refines := [("tiny", (.int, []))] }
private def proof (name : String) (upper lower : Ty) (dummy : Bool := false) : Local := {
  name, slot := 0, ty := (Bound.mk upper lower).ty, mutable := false, typeValue := dummy }
private def context (locals : List Local) : Ctx := {
  sigs := [], sigProg := { fns := [], main := 0 }, types, locals }
private def viewIs (ctx : Ctx) (source : Ty) (expected : Option Ty) : Bool :=
  match ctx.formattingView p source with
  | .ok actual => actual == expected
  | .error _ => false

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "expected an artifact directory")
  need "integer capability formats an opaque input"
    (viewIs (context [proof "D" .int t]) t (some .int))
  need "char32 does not become an int merely because its Core storage is int"
    (viewIs (context [proof "D" .char32 t]) t (some .char32))
  need "a refinement capability composes with its printable numeric base"
    (viewIs (context [proof "D" (.refine "tiny") t]) t (some .int))
  for ctx in [context [], context [proof "D" .int t true]] do
    need "static facts and dummy proofs cannot authorize formatting" (viewIs ctx t none)
  need "a rational-only bound does not invent integer formatting"
    (viewIs (context [proof "D" .rational t]) t none)
  need "a discard bound does not invent a printable value"
    (viewIs (context [proof "D" .void t]) t none)
  need "component capabilities can establish a string view"
    (viewIs (context [proof "Element" .char a]) (.arr a) (some Ty.string))
  let composed := context [proof "Whole" (.arr a) t, proof "Element" .char a]
  need "whole and component proofs can compose to a printable string"
    (viewIs composed t (some Ty.string))
  need "a whole-array proof alone cannot invent its element conversion"
    (viewIs (context [proof "Whole" (.arr a) t]) t none)
  need "concrete printable inputs do not change domains from ambient proofs"
    (viewIs (context [proof "Other" .float .int]) .int none)
  for locals in [[proof "I" .int t, proof "F" .float t],
      [proof "F" .float t, proof "I" .int t]] do
    need "unrelated printable domains remain ambiguous in either order"
      (match (context locals).formattingView p t with | .error _ => true | _ => false)
  let entries := [
    ("format-entry-char32", "Main():void={}", "0u03BB", "λ\n"),
    ("format-entry-refinement", "small:=type{_X:int where 0<=_X,_X<=10}\nValue()<computes>:small=3\nMain():void={}", "Value()", "3\n"),
    ("format-entry-float", "small:=type{_X:float where 0.0<=_X,_X<=10.0}\nValue()<computes>:small=2.5\nMain():void={}", "Value()", "2.500000\n"),
    ("format-entry-fallback", "Value()<transacts>:[]int=(Print(\"once\");array{7})\nMain():void={}", "Value()", "once\n")]
  for (name, source, expression, expected) in entries do
    let entry ← getOK s!"{name}: parse entry" (parseExprText expression)
    let entry := SExpr.app p (.ident p "$Show") [entry] false
    let compiled ← getOK s!"{name}: compile" (compileChecked source { entry := some entry })
    need s!"{name}: checked Core" (compiled.prog.check && compiled.prog.checkControl &&
      compiled.prog.checkTypes compiled.sigs compiled.slotTys)
    let output ← match compiled.prog.runB 1000000 10000 with
      | .res (.ok _, bytes) => pure (ByteArray.mk (bytes.map Nat.toUInt8).toArray)
      | _ => throw (IO.userError s!"{name}: run failed")
    need s!"{name}: exact entry oracle" (output == expected.toUTF8)
    let strict ← getOK s!"{name}: choice-free compile"
      (compileChecked source { entry := some entry, profile := .choiceFree })
    need s!"{name}: identical admitted bytecode" (compiled.prog.encode == strict.prog.encode)
    IO.FS.writeBinFile s!"{out}/{name}.vbc" compiled.prog.encode
    IO.FS.writeBinFile s!"{out}/{name}.expected" expected.toUTF8
  IO.println "bound formatting contracts passed (actual/composed views, domains and exact entry oracles)"
