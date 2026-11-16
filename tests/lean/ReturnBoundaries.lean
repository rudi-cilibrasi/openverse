import OpenVerse
open OpenVerse OpenVerse.Front
private def source (execute internally : Bool) : String :=
  let callable := "type{_()<computes>:int}"
  "One()<computes>:int=1\n" ++
  "Many(V:" ++ callable ++ ",N:int)<computes>:" ++ callable ++ "=\n" ++
  "    for(I:=1..N):\n" ++
  "        if(I=1):\n" ++
  (if internally then "            Ignored:=V()\n" else "") ++
  "            return V\n" ++
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
def main (args : List String) : IO Unit := do
  let out := args.headD "/tmp/openverse-return-metadata"
  IO.FS.createDirAll out
  for extended in [false, true] do
    for (execute, internally) in [(false,false),(true,false),(false,true)] do
      for dummy in [false,true] do
        let expected := !dummy || (!execute && !internally)
        match compile (source execute internally) dummy extended with
        | .ok c =>
          IO.println s!"{extended}/{execute}/{internally}/{dummy}: admitted"
          unless expected && c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys do
            throw <| IO.userError "unexpected admission or bad Core"
          match c.prog.runB 1000000 1000 with
          | .res (.ok _, output) => unless String.ofList (output.map Char.ofNat) == "1\n" do throw <| IO.userError "bad oracle"
          | _ => throw <| IO.userError "bad runtime"
          IO.FS.writeBinFile s!"{out}/{extended}-{execute}-{internally}-{dummy}.vbc" c.prog.encode
        | .error message =>
          IO.println s!"{extended}/{execute}/{internally}/{dummy}: {message}"
          if expected || !(message.splitOn "dummy type value cannot").length > 1 then
            throw <| IO.userError "unexpected refusal"
