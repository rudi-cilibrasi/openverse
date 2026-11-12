import OpenVerse.Front.Elab
import OpenVerse.Core.Bounded
import OpenVerse.Core.Encode

open OpenVerse OpenVerse.Front

/-- Development acceptance tests for #502. These intentionally fail while
    source bounds remain guarded; the ordinary gate uses the API contracts. -/
def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "expected a fresh output directory")
  let positive := ["process", "holder", "value", "refined", "choice-valid", "default-valid",
    "context", "override-valid", "receiver-override", "state", "cancel", "interior-path",
    "interior-containers", "interior-nested", "interior-state", "interior-cancel", "overload",
    "overload-shapes", "overload-values", "overload-inherited", "overload-projected", "overload-state",
    "peer-tuple-value", "peer-tuple-values", "peer-tuple-method", "peer-tuple-unique", "peer-numeric", "peer-any",
    "peer-inference", "peer-state", "peer-cancel", "peer-containers-control", "peer-containers",
    "peer-container-inference", "peer-map-keys", "peer-refinement", "peer-tuple-array",
    "choice-numeric-bound", "choice-numeric-bound-control", "choice-method-bound", "choice-method-bound-control",
    "choice-index-bound", "choice-index-bound-control", "choice-method-bound-only", "choice-method-varying-bound",
    "choice-method-primitive-peer", "choice-method-primitive-peer-control", "choice-method-domain",
    "peer-void", "peer-void-control", "bottom-flow", "bottom-flow-control",
    "peer-void-join", "peer-void-join-control", "peer-void-comparable", "peer-void-comparable-control",
    "peer-void-tuple-value", "peer-void-tuple-value-control",
    "peer-numeric-comparable", "peer-numeric-comparable-control",
    "choice-nested-spawn-bound", "choice-nested-spawn-bound-control",
    "choice-class-method",
    "choice-class-method-control",
    "choice-class-mono",
    "choice-class-mono-control",
    "choice-class-unique",
    "choice-class-unique-control",
    "choice-class-bound-only",
    "choice-class-bound-only-control",
    "choice-class-state",
    "choice-class-state-control", "choice-class-varying", "choice-class-varying-control",
    "choice-class-compound", "choice-class-compound-control",
    "choice-class-fields", "choice-class-fields-control"]
  let negative := ["choice-refusal", "default-refusal", "override-refusal", "overload-interface-refusal",
    "overload-ancestor-refusal", "overload-optional-refusal", "overload-empty-refusal", "overload-scope-refusal",
    "overload-value-refusal", "interior-readonly-refusal", "interior-effect-refusal",
    "peer-tuple-comparable-refusal", "peer-tuple-relation-refusal", "peer-narrow-refusal", "peer-float-refusal",
    "peer-map-key-refusal", "peer-container-arity-refusal", "peer-container-narrow-refusal",
    "peer-refinement-narrow-refusal", "peer-refinement-literal-refusal", "default-undeclared-bound-refusal",
    "choice-method-bound-refusal", "peer-void-narrow-refusal", "peer-void-comparable-refusal",
    "peer-comparable-equality-refusal", "choice-class-unproved-refusal"]
  let mut failures := 0
  for name in positive ++ negative do
    let root := s!"tests/upper-bounds/{name}"
    let source ← IO.FS.readFile (root ++ ".verse")
    let result := parseProgram source >>= elabProgram
    if negative.contains name then
      let fragment := (← IO.FS.readFile (root ++ ".error")).trimAscii.toString
      match result with
      | .error message =>
        if (message.splitOn fragment).length > 1 then IO.println s!"ok {name}: refused"
        else
          IO.eprintln s!"FAIL {name}: wrong refusal: {message}"
          failures := failures + 1
      | .ok _ =>
        IO.eprintln s!"FAIL {name}: accepted an invalid bound"
        failures := failures + 1
    else match result with
      | .error message =>
        IO.eprintln s!"FAIL {name}: {message}"
        failures := failures + 1
      | .ok compiled =>
        let expected ← IO.FS.readBinFile (root ++ ".expected")
        let checked := compiled.prog.check && compiled.prog.checkControl &&
          compiled.prog.checkTypes compiled.sigs compiled.slotTys
        let correct := match compiled.prog.runB 1000000 10000 with
          | .res (.ok _, output) => ByteArray.mk (output.map Nat.toUInt8).toArray == expected
          | _ => false
        if !checked || !correct then
          IO.eprintln s!"FAIL {name}: Core admission or independent output oracle"
          failures := failures + 1
        else
          IO.FS.writeBinFile s!"{out}/{name}.vbc" compiled.prog.encode
          IO.FS.writeBinFile s!"{out}/{name}.expected" expected
          IO.println s!"ok {name}: checked Lean oracle"
  if failures != 0 then throw (IO.userError s!"upper-bound source contract: {failures} failure(s)")
