import OpenVerse
open OpenVerse OpenVerse.Front
private def source (execute internally : Bool) : String :=
  let callable := "type{_()<computes>:int}"
  "One()<computes>:int=1\n" ++
  "Many(V:" ++ callable ++ ",N:int)<computes>:" ++ callable ++ "=\n" ++
  "    for(I:=1..N):\n" ++
  "        if(I=1):\n" ++
  (if internally then "            Ignored:=V()\n" else "") ++
  "            return V|V\n" ++
  "    V|V\n" ++
  "Caller(F:" ++ callable ++ ",Dummy:" ++ callable ++ ")<computes>:int=\n" ++
  "    Rows:=for(G:=Many(Dummy,2)):" ++ (if execute then "G()" else "1") ++
  "\n    Rows.Length\nMain():void=Print(\"{Caller(One,One)}\")\n"
private def compile (text : String) (dummy extended : Bool) : Except String Compiled := do
  let tops ← parseProgram text
  let tops := tops.map fun
    | .fn p name ps tps specs ret body => .fn p name (ps.map fun param =>
      { param with typeValue := dummy && name == "Caller" && param.name == "Dummy" }) tps specs ret body
    | top => top
  elabProgram tops { extendedDefaults := extended }
private def check (out tag text : String) (dummy extended expected : Bool)
    (stdout refusal : String) : IO Unit := do
  match compile text dummy extended with
  | .ok c =>
    unless expected && c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys do
      throw (IO.userError s!"unexpected admission or bad Core: {tag}")
    match c.prog.runB 1000000 1000 with
    | .res (.ok _, output) =>
      unless String.ofList (output.map Char.ofNat) == stdout do throw (IO.userError s!"bad oracle: {tag}")
    | _ => throw (IO.userError s!"bad runtime: {tag}")
    IO.FS.writeBinFile s!"{out}/{tag}.vbc" c.prog.encode
    IO.FS.writeFile s!"{out}/{tag}.expected" stdout
  | .error message =>
    if expected || !(message.splitOn refusal).length > 1 then
      throw (IO.userError s!"unexpected refusal: {tag}: {message}")
def main (args : List String) : IO Unit := do
  let out := args.headD "/tmp/openverse-loop-operands-api"
  IO.FS.createDirAll out
  for extended in [false,true] do
    for (execute, internally) in [(false,false),(true,false),(false,true)] do
      for dummy in [false,true] do
        check out s!"forward-{extended}-{execute}-{internally}-{dummy}" (source execute internally)
          dummy extended (!dummy || (!execute && !internally)) "2\n" "dummy type value cannot"
    for safe in [false,true] do
      let text ← IO.FS.readFile s!"tests/fixtures/loop-return-operands/loop-metadata-{if safe then "safe" else "bad"}-exec.verse"
      for dummy in [false,true] do
        let value := if safe then 11 else 22
        check out s!"exec-{extended}-{safe}-{dummy}" text dummy extended (safe || !dummy)
          s!"got {value}\ngot {value}\ncount 2\n" "dummy type value cannot"
    -- No consumer or constructor survives in Main, but the boxed generic
    -- helper signature still needs the private cell class registered.
    let unused ← IO.FS.readFile "tests/fixtures/loop-return-operands/generic-unused.verse"
    match compile unused false extended with
    | .ok c => unless c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys do
        throw (IO.userError "unused generic cell Core mismatch")
    | .error message => throw (IO.userError s!"unused generic cell refusal: {message}")
    for fixture in ["loop-evidence-capture", "choice-loop-local-evidence"] do
      let evidence ← IO.FS.readFile s!"tests/fixtures/loop-return-operands/{fixture}.verse"
      for dummy in [false,true] do
        let result : Except String Compiled := do
          let tops ← parseProgram evidence
          let rename (name : String) : Except String String :=
            pure (if name == "evidence" then SubtypeEvidence.family else name)
          let tops ← tops.mapM fun
            | .fn p name params tparams specs ret body => do
              let params ← params.mapM fun param => do
                let ty ← param.ty.mapNamesM rename
                pure { param with ty := ty, typeValue := dummy && name == "F" && param.name == "D" }
              pure (.fn p name params tparams specs (← ret.mapNamesM rename) body)
            | top => pure top
          elabProgram tops { extendedDefaults := extended }
        match result with
        | .ok c => unless !dummy && c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys do
            throw (IO.userError "implicit proof admission or Core mismatch")
        | .error message => unless dummy && (message.splitOn "has no member 'N'").length > 1 do
            throw (IO.userError s!"implicit proof refusal: {message}")
  IO.println "loop operand API passed (30 classifications, 14 complete Lean oracles, operational proof roles)"
