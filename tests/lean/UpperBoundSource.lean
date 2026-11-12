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
    "choice-class-fields", "choice-class-fields-control",
    "choice-class-waiting-value", "choice-class-waiting-value-control",
    "bound-method-families", "bound-method-families-control", "bound-refine-contexts", "bound-refine-contexts-control",
    "bound-return-frames", "bound-return-frames-control", "bound-frame-cells-break", "bound-frame-cells-break-control"]
  let fifo := ["fifo-bound-promotion", "fifo-bound-promotion-control",
    "fifo-bound-woken", "fifo-bound-woken-control", "fifo-bound-spawn", "fifo-bound-spawn-control",
    "fifo-bound-two-losers", "fifo-bound-two-losers-control", "fifo-bound-sleep", "fifo-bound-sleep-control"]
  let methodValues := ["method-value-argument", "method-value-argument-control",
    "method-value-result", "method-value-result-control", "method-value-state", "method-value-state-control",
    "method-value-cancel", "method-value-cancel-control"]
  let callables := ["callable-upper", "callable-upper-control", "callable-default", "callable-default-control",
    "callable-state", "callable-state-control", "callable-waiting", "callable-waiting-control",
    "callable-decides", "callable-decides-control", "callable-bound-only", "callable-bound-only-control",
    "callable-generic", "callable-generic-control"]
  let containers := ["container-view-basic", "container-view-basic-control",
    "container-view-state", "container-view-state-control", "container-view-waiting", "container-view-waiting-control",
    "container-view-generic", "container-view-generic-control", "container-view-interior", "container-view-interior-control",
    "container-view-concat", "container-view-concat-control"]
  let iterators := ["container-view-iteration", "container-view-iteration-control",
    "container-view-iteration-state", "container-view-iteration-state-control"]
  let operators := ["bound-array-join", "bound-array-join-control",
    "bound-array-join-state", "bound-array-join-state-control",
    "bound-numeric-operators", "bound-numeric-operators-control", "bound-numeric-state", "bound-numeric-state-control"]
  let profiled := fifo ++ methodValues ++ callables ++ containers ++ operators ++
    ["bound-refine-contexts", "bound-refine-contexts-control"]
  let negative := ["choice-refusal", "default-refusal", "override-refusal", "overload-interface-refusal",
    "overload-ancestor-refusal", "overload-optional-refusal", "overload-empty-refusal", "overload-scope-refusal",
    "overload-value-refusal", "interior-readonly-refusal", "interior-effect-refusal",
    "peer-tuple-comparable-refusal", "peer-tuple-relation-refusal", "peer-narrow-refusal", "peer-float-refusal",
    "peer-map-key-refusal", "peer-container-arity-refusal", "peer-container-narrow-refusal",
    "peer-refinement-narrow-refusal", "peer-refinement-literal-refusal", "default-undeclared-bound-refusal",
    "choice-method-bound-refusal", "peer-void-narrow-refusal", "peer-void-comparable-refusal",
    "peer-comparable-equality-refusal", "choice-class-unproved-refusal",
    "method-value-argument-refusal", "method-value-result-refusal",
    "method-value-stored-refusal", "method-value-stored-control-refusal",
    "callable-bracket-refusal", "callable-decides-refusal", "callable-suspends-refusal",
    "callable-effect-refusal", "callable-effect-control-refusal", "callable-unproved-refusal",
    "container-view-unproved-refusal", "container-view-query-unproved-refusal", "container-view-element-refusal",
    "container-view-method-refusal", "container-view-effect-refusal", "container-view-storage-refusal",
    "container-view-iteration-unproved-refusal", "container-view-concat-unproved-refusal",
    "container-view-iteration-element-refusal", "container-view-iteration-effect-refusal",
    "container-view-iteration-effect-control-refusal", "bound-numeric-unproved-refusal",
    "bound-numeric-mixed-refusal", "bound-numeric-mixed-control-refusal", "bound-numeric-narrow-refusal",
    "bound-numeric-floor-bracket-refusal", "bound-numeric-comparison-unproved-refusal",
    "bound-array-join-unproved-refusal", "bound-array-join-narrow-refusal"]
  let mut failures := 0
  let cases := (positive ++ fifo ++ methodValues ++ callables ++ containers ++ iterators ++ operators ++ negative).map (fun name => (name, fifo.contains name, name)) ++
    ["fifo-bound-sleep", "fifo-bound-sleep-control"].map (fun name => (name, false, name ++ "-default"))
  for (name, eventFifo, artifact) in cases do
    let root := s!"tests/upper-bounds/{name}"
    let source ← IO.FS.readFile (root ++ ".verse")
    let result := parseProgram source >>= fun tops => elabProgram tops { eventFifo }
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
          if iterators.contains name then
            match parseProgram source >>= fun tops =>
                elabProgram tops { eventFifo, profile := .choiceFree } with
            | .error message =>
              unless (message.splitOn "--no-choice excludes for").length > 1 do
                throw (IO.userError s!"{artifact}: wrong choice-free refusal: {message}")
            | .ok _ => throw (IO.userError s!"{artifact}: --no-choice admitted collection iteration")
          if profiled.contains name then
            let strict ← match parseProgram source >>= fun tops =>
                elabProgram tops { eventFifo, profile := .choiceFree } with
              | .ok strict => pure strict
              | .error message => throw (IO.userError s!"{artifact}: --no-choice refused: {message}")
            unless strict.prog.encode == compiled.prog.encode do
              throw (IO.userError s!"{artifact}: --no-choice changed admitted bytecode")
          IO.FS.writeBinFile s!"{out}/{artifact}.vbc" compiled.prog.encode
          IO.FS.writeBinFile s!"{out}/{artifact}.expected" expected
          IO.println s!"ok {artifact}: checked Lean oracle"
  if failures != 0 then throw (IO.userError s!"upper-bound source contract: {failures} failure(s)")
