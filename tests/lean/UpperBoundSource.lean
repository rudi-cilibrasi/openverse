import OpenVerse.Front.Elab
import OpenVerse.Core.Bounded
import OpenVerse.Core.Encode

open OpenVerse OpenVerse.Front

/-- Development acceptance tests for #502. These intentionally fail while
    source bounds remain guarded; the ordinary gate uses the API contracts. -/
def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "expected a fresh output directory")
  let positive := ["process", "holder", "value", "refined", "choice-valid", "default-valid",
    "context", "override-valid", "receiver-override", "state", "cancel", "interior-path", "overload",
    "overload-shapes", "overload-values", "overload-inherited", "overload-projected", "overload-state", "peer-tuple-value"]
  let negative := ["choice-refusal", "default-refusal", "override-refusal", "overload-interface-refusal",
    "overload-ancestor-refusal", "overload-optional-refusal", "overload-empty-refusal", "overload-scope-refusal",
    "overload-value-refusal"]
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
