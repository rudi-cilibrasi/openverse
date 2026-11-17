import OpenVerse.Front.Elab
import OpenVerse.Core.Bounded
import OpenVerse.Core.Encode

open OpenVerse OpenVerse.Front

-- Every negative has an executable all-real control. The literal failed
-- local-copy conditions preserve original values; observers must not disappear.
-- A distinct real B.A read does not observe write-only private Stored.
-- Live-after-heap and metadata-in-B.A companions remain in MetadataPrivateStores.
private def cases : List (String × String × Bool × String) := [
  ("direct-original", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\na:=class<computes>{M()<computes>:int=1|2}\nb:=class<computes>{M()<computes>:int=3|4}\nDup(V:t where t:type)<computes>:t=V|V\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(),B:=Dup(a{})|Dup(b{}),Y:=B.M()):\n        if(set Stored=Dummy;false?){}\n        Sleep(0.001)\n        F()\n    Rows.Length\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", true, "64\n"),
  ("stored-original", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\na:=class<computes>{M()<computes>:int=1|2}\nb:=class<computes>{M()<computes>:int=3|4}\nDup(V:t where t:type)<computes>:t=V|V\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(),B:=Dup(a{})|Dup(b{}),Y:=B.M()):\n        if(set Stored=Dummy;false?){}\n        Sleep(0.001)\n        Stored()\n    Rows.Length\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", true, "64\n"),
  ("immediate", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n    var Stored:type{_()<computes>:int}=F\n    if(set Stored=Dummy;false?){}\n    F()\nMain()<transacts>:void=Print(\"{Caller(One,Two)}\")\n", true, "1\n"),
  ("plain-no-wait", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    if(set Stored=Dummy;false?){}\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", true, "1\n"),
  ("plain-stored", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    if(set Stored=Dummy;false?){}\n    Sleep(0.001)\n    Stored()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", true, "1\n"),
  ("plain", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    if(set Stored=Dummy;false?){}\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", true, "1\n"),
  ("range", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    R:=for(N:=1..1):\n        if(set Stored=Dummy;false?){}\n        Sleep(0.001)\n        F()\n    R.Length\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", true, "1\n"),
  ("cancellation-read", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    R:=race:\n        block:\n            defer:\n                Value:=Dummy()\n            Sleep(1.0)\n            0\n        block:\n            Sleep(0.001)\n            0\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("cancellation-write", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    R:=race:\n        block:\n            defer:\n                set Stored=Dummy\n            Sleep(1.0)\n            0\n        block:\n            Sleep(0.001)\n            0\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("cleanup-direct-read", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    defer:\n        Value:=Dummy()\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("cleanup-direct-write", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    defer:\n        set Stored=Dummy\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("committed", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    if(set Stored=Dummy;true?){}\n    Stored()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "2\n"),
  ("condition-cleanup", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    if(block{defer{Value:=Stored()};set Stored=Dummy;false?}){}\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("direct-observer", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    if(set Stored=Dummy;Stored();false?){}\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("initial-dummy", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    if(set Stored=F;false?){}\n    Sleep(0.001)\n    Stored()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "2\n"),
  ("observer-call", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    if(set Stored=Dummy;Use(Stored);false?){}\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("saved-alias", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    Saved:=Stored\n    set Stored=F\n    if(set Stored=Dummy;false?){}\n    Sleep(0.001)\n    Saved()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "2\n"),
  ("signal", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    E:=event(int){}\n    branch:\n        E.Await()\n        Value:=Stored()\n    if(set Stored=Dummy;E.Signal(0);false?){}\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("wait", "One()<computes>:int=1\nTwo()<computes>:int=2\nUse(G:type{_()<computes>:int})<computes>:int=G()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Dummy\n    Sleep(0.001)\n    Stored()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "2\n"),
  ("copy-chain", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    var Scratch:type{_()<computes>:int}=F\n    if(set Stored=Dummy;set Scratch=Stored;false?){Print(\"bad\")}\n    Stored()+Scratch()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", true, "result 22\n"),
  ("nested-rhs", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    if(set Stored=block{Temp:=Dummy;Temp};false?){Print(\"bad\")}\n    Stored()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", true, "result 11\n"),
  ("real-cleanup", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    B:=box(type{_()<computes>:int}){A:=F}\n    defer:Print(\"cleanup {B.A()}\")\n    if(set Stored=Dummy;false?){Print(\"bad\")}\n    Stored()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", true, "cleanup 11\nresult 11\n"),
  ("write-only-unrelated-heap-read", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    B:=box(type{_()<computes>:int}){A:=F}\n    if(set Stored=Dummy;B.A()>0;false?){Print(\"bad\")}\n    F()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", true, "result 11\n"),
  ("cleanup-field-alias", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    B:=box(type{_()<computes>:int}){A:=Dummy}\n    defer:Print(\"cleanup {B.A()}\")\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", false, "cleanup 22\nresult 11\n"),
  ("shared-heap-write", "One()<computes>:int=1\nTwo()<computes>:int=2\nfnbox:=class{var Value:type{_()<computes>:int}}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    B:=fnbox{Value:=F}\n    if(set B.Value=Dummy;false?){}\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n")
 ]

private def compile (source : String) (dummy extended : Bool) : Except String Compiled := do
  let tops ← parseProgram source
  let tops := tops.map fun
    | .fn p name ps tps specs ret body => .fn p name (ps.map fun param =>
      { param with typeValue := dummy && name == "Caller" && param.name == "Dummy" }) tps specs ret body
    | top => top
  elabProgram tops { extendedDefaults := extended }

def main (args : List String) : IO Unit := do
  if args == ["--count"] then
    IO.println cases.length
    return
  let some index := args[0]?.bind String.toNat? | throw <| IO.userError "expected case index"
  let some (name, source, accepted, output) := cases[index]? | throw <| IO.userError "invalid case index"
  let some path := (args[1]? : Option String) | throw <| IO.userError "expected artifact directory"
  for extended in [false, true] do
    for dummy in [false, true] do
      match compile source dummy extended with
      | .ok c =>
        unless !dummy || accepted do
          throw <| IO.userError s!"{name}: unexpectedly admitted metadata"
        unless c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys do
          throw <| IO.userError s!"{name}: invalid Core"
        match c.prog.runB 10000000 10000 with
        | .res (.ok _, actual) =>
          unless String.ofList (actual.map Char.ofNat) == output do
            throw <| IO.userError s!"{name}: incomplete runtime oracle"
        | _ => throw <| IO.userError s!"{name}: VM failure"
        let artifact := s!"{path}/{index}-{extended}-{dummy}"
        IO.FS.writeBinFile (artifact ++ ".vbc") c.prog.encode
        IO.FS.writeFile (artifact ++ ".expected") output
      | .error message =>
        if !dummy || accepted || !(message.splitOn "dummy type value cannot").length > 1 then
          throw <| IO.userError s!"{name}: unexpected refusal: {message}"
  IO.println s!"metadata local-rollback case passed: {name}"
