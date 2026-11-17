import OpenVerse
open OpenVerse OpenVerse.Front

private def source (execute internally normal : Bool) : String :=
  let callable := "type{_()<computes>:int}"
  "One()<computes>:int=1\n" ++
  "Many(V:" ++ callable ++ ",N:int)<computes>:" ++ callable ++ "=\n" ++
  (if internally then "    Ignored:=V()\n" else "") ++
  "    Y:=if(N>0)then(return V)else(V|V)\n    Y|Y\n" ++
  "Caller(F:" ++ callable ++ ",Dummy:" ++ callable ++ ")<computes>:int=\n" ++
  "    Rows:=for(G:=Many(Dummy," ++ (if normal then "0" else "2") ++ ")):" ++
  (if execute then "G()" else "1") ++
  "\n    Rows.Length\nMain():void=Print(\"{Caller(One,One)}\")\n"

private def compile (text : String) (dummy extended : Bool) : Except String Compiled := do
  let tops ← parseProgram text
  let tops := tops.map fun
    | .fn p name ps tps specs ret body => .fn p name (ps.map fun param =>
      { param with typeValue := dummy && name == "Caller" && param.name == "Dummy" }) tps specs ret body
    | top => top
  elabProgram tops { extendedDefaults := extended }

def main (args : List String) : IO Unit := do
  let out := args.headD "/tmp/openverse-initializer-choice-metadata"
  IO.FS.createDirAll out
  for extended in [false, true] do
    for normal in [false, true] do
      for (execute, internally) in [(false,false),(true,false),(false,true)] do
        for dummy in [false,true] do
          let expected := !dummy || (!execute && !internally)
          match compile (source execute internally normal) dummy extended with
          | .ok compiled =>
            unless expected && compiled.prog.check && compiled.prog.checkControl &&
                compiled.prog.checkTypes compiled.sigs compiled.slotTys do
              throw <| IO.userError "unexpected initializer admission or invalid Core"
            let stdout := if normal then "4\n" else "1\n"
            match compiled.prog.runB 1000000 1000 with
            | .res (.ok _, output) =>
              unless String.ofList (output.map Char.ofNat) == stdout do
                throw <| IO.userError "initializer metadata runtime mismatch"
            | _ => throw <| IO.userError "initializer metadata runtime failed"
            let artifact := s!"{out}/{extended}-{normal}-{execute}-{internally}-{dummy}"
            IO.FS.writeBinFile (artifact ++ ".vbc") compiled.prog.encode
            IO.FS.writeFile (artifact ++ ".expected") stdout
          | .error message =>
            if expected || !(message.splitOn "dummy type value cannot").length > 1 then
              throw <| IO.userError s!"unexpected initializer refusal: {message}"
  IO.println "initializer metadata contracts passed (24 classifications, 16 complete runtime oracles)"
