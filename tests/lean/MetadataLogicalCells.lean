/- Paired ordinary-source controls for logical-cell metadata precision. -/
import OpenVerse
open OpenVerse OpenVerse.Front

private def compile (source : String) (metadata extended : Bool) : Except String Compiled := do
  let tops ← parseProgram source
  let tops := tops.map fun
    | .fn p name params tparams specs ret body =>
      .fn p name (params.map fun param =>
        { param with typeValue := metadata && name == "Caller" && param.name == "Dummy" })
        tparams specs ret body
    | other => other
  elabProgram tops { extendedDefaults := extended }

private def check (out tag text expected : String) (metadata extended admitted : Bool) : IO Unit := do
  match compile text metadata extended with
  | .error message =>
    unless !admitted && (message.splitOn "dummy type value cannot").length > 1 do
      throw (IO.userError s!"unexpected logical-cell refusal: {tag}: {message}")
  | .ok compiled =>
    unless admitted && compiled.prog.check && compiled.prog.checkControl &&
        compiled.prog.checkTypes compiled.sigs compiled.slotTys do
      throw (IO.userError s!"unexpected logical-cell admission/Core mismatch: {tag}")
    match compiled.prog.runB 10000000 10000 with
    | .res (.ok _, output) =>
      unless String.ofList (output.map Char.ofNat) == expected do
        throw (IO.userError s!"logical-cell output mismatch: {tag}")
    | _ => throw (IO.userError s!"logical-cell VM failure: {tag}")
    IO.FS.writeBinFile s!"{out}/{tag}.vbc" compiled.prog.encode
    IO.FS.writeFile s!"{out}/{tag}.expected" expected

def main (args : List String) : IO Unit := do
  let out := args.headD "/tmp/openverse-logical-cell-source"
  IO.FS.createDirAll out
  let cases : List (String × Bool × String) := [
    ("saved-real-snapshot", true, "value 1\nvalue 1\n"),
    ("saved-metadata-snapshot", false, "value 2\nvalue 2\n"),
    ("two-cells-real-result", true, "value 1\nvalue 1\n"),
    ("two-cells-metadata-result", false, "value 2\nvalue 2\n"),
    ("cleanup-taints-next", false, "value 1\nvalue 2\n"),
    ("cleanup-resets-after-save", false, "value 2\nvalue 1\n"),
    ("cleanup-taint-opaque", true, "row\nrow\n"),
    ("operand-resets-cell", false, "value 1\nvalue 1\n"),
    ("operand-taints-next", false, "value 1\nvalue 2\n"),
    ("tuple-real-column", true, "value 1\nvalue 1\n"),
    ("tuple-metadata-column", false, "value 2\nvalue 2\n"),
    ("nested-tuple-real-column", false, "value 1\nvalue 1\n"),
    ("nested-tuple-metadata-column", false, "value 2\nvalue 2\n"),
    ("nested-real-reader-wrap", true, "row\nrow\n"),
    ("recursive-reader", true, "v 7\nv 8\n"),
    ("projected-private-exec", false, "row\nrow\n"),
    ("projected-object-exec", false, "row\nrow\n"),
    ("dormant-first-execute", false, ""),
    ("dormant-first-opaque", true, ""),
    ("live-first-execute", false, "value 0\n"),
    ("live-first-opaque", true, "value 1\n")]
  for (name, metadataAllowed, expected) in cases do
    for control in [false,true] do
      let suffix := if control then "-control" else ""
      let source ← IO.FS.readFile s!"tests/fixtures/logical-cell-metadata/{name}{suffix}.verse"
      for extended in [false,true] do
        for metadata in [false,true] do
          let start ← IO.monoMsNow
          check out s!"{name}-{control}-{extended}-{metadata}" source expected metadata extended
            (!metadata || metadataAllowed)
          IO.println s!"{name} control={control} extended={extended} metadata={metadata} elapsed_ms={(← IO.monoMsNow) - start}"
          (← IO.getStdout).flush
  IO.println "logical-cell source: 168 API classifications, 116 complete Lean oracles"
