import OpenVerse.Front.Elab
import OpenVerse.Core.Bounded
import OpenVerse.Core.Encode

open OpenVerse OpenVerse.Front

private def cases : List (String × String × Bool × String) := [
  ("write-only-loop", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    var N:int=0\n    loop:\n        if(N>0)then set Stored=Dummy\n        set Stored=F\n        Sleep(0.01)\n        set N+=1\n        if(N>=2)then break\n    0\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", true, "0\n"),
  ("loop-read-before-overwrite", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    var N:int=0\n    loop:\n        if(N>0)then set Stored=Dummy\n        Ignored:=Stored()\n        set Stored=F\n        Sleep(0.01)\n        set N+=1\n        if(N>=2)then break\n    0\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "0\n"),
  ("loop-final-read", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    var N:int=0\n    loop:\n        if(N>0)then set Stored=Dummy\n        set Stored=F\n        Sleep(0.01)\n        set N+=1\n        if(N>=2)then break\n    Ignored:=Stored()\n    0\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "0\n"),
  ("dead-frame", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Dummy\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", true, "1\n"),
  ("borrowed-helper", "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two\na:=class<computes>{M()<computes>:int=1|2}\nb:=class<computes>{M()<computes>:int=3|4}\nDup(V:t where t:type)<computes>:t=V|V\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(),B:=Dup(a{})|Dup(b{}),Y:=B.M()):\n        set Stored=Dummy\n        Sleep(0.001)\n        F()\n    Rows.Length\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "64\n"),
  ("cleanup-read", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    defer:\n        Value:=Stored()\n    set Stored=Dummy\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("concurrent-reader", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    branch:\n        Sleep(0.001)\n        Value:=Stored()\n    set Stored=Dummy\n    Sleep(0.01)\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("dead-immediate", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Dummy\n    F()\nMain()<transacts>:void=Print(\"{Caller(One,Two)}\")\n", true, "1\n"),
  ("dead-no-wait", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Dummy\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", true, "1\n"),
  ("live-read", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Dummy\n    Sleep(0.001)\n    Stored()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "2\n"),
  ("rhs-exec", "One()<computes>:int=1\nTwo()<computes>:int=2\nObserve(G:type{_()<computes>:int},R:type{_()<computes>:int})<computes>:type{_()<computes>:int}=\n    Ignored:=G()\n    R\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Observe(Dummy,F)\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("rhs-print", "One()<computes>:int=1\nTwo()<computes>:int=2\nMake(R:type{_()<computes>:int})<transacts>:type{_()<computes>:int}=\n    Print(\"rhs\")\n    R\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Make(Dummy)\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "rhs\n1\n"),
  ("saved-real", "One()<computes>:int=1\nTwo()<computes>:int=2\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    Saved:=Stored\n    set Stored=Dummy\n    Sleep(0.001)\n    Saved()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("transitive-fork", "One()<computes>:int=1\nTwo()<computes>:int=2\nForkIt()<suspends>:void=\n    branch:\n        Sleep(0.001)\n        0\n    ()\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Dummy\n    ForkIt()\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("transitive-signal", "One()<computes>:int=1\nTwo()<computes>:int=2\nSignalIt(E:event(int))<suspends>:void=E.Signal(0)\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    E:=event(int){}\n    set Stored=Dummy\n    SignalIt(E)\n    F()\nMain()<suspends>:void=Print(\"{Caller(One,Two)}\")\n", false, "1\n"),
  ("dead-wait", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nObserve(G:type{_()<computes>:int},R:type{_()<computes>:int})<computes>:type{_()<computes>:int}=block{Ignored:=G();R}\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Dummy\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", true, "result 11\n"),
  ("dead-heap", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nObserve(G:type{_()<computes>:int},R:type{_()<computes>:int})<computes>:type{_()<computes>:int}=block{Ignored:=G();R}\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    B:=box(type{_()<computes>:int}){A:=F}\n    if(set Stored=Dummy;B.A()>0;false?){Print(\"bad\")}\n    F()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", true, "result 11\n"),
  ("dead-initial-metadata", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nObserve(G:type{_()<computes>:int},R:type{_()<computes>:int})<computes>:type{_()<computes>:int}=block{Ignored:=G();R}\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    set Stored=F\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", true, "result 11\n"),
  ("independent-heap-observer", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nObserve(G:type{_()<computes>:int},R:type{_()<computes>:int})<computes>:type{_()<computes>:int}=block{Ignored:=G();R}\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    B:=box(type{_()<computes>:int}){A:=Dummy}\n    if(set Stored=Dummy;B.A()>0;false?){Print(\"bad\")}\n    F()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", false, "result 11\n"),
  ("local-observer", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nObserve(G:type{_()<computes>:int},R:type{_()<computes>:int})<computes>:type{_()<computes>:int}=block{Ignored:=G();R}\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    if(set Stored=Dummy;Stored()>0;false?){Print(\"bad\")}\n    F()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", false, "result 11\n"),
  ("live-after-heap", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nObserve(G:type{_()<computes>:int},R:type{_()<computes>:int})<computes>:type{_()<computes>:int}=block{Ignored:=G();R}\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    B:=box(type{_()<computes>:int}){A:=F}\n    if(set Stored=Dummy;B.A()>0;false?){Print(\"bad\")}\n    Stored()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", false, "result 11\n"),
  ("rhs-observer", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nObserve(G:type{_()<computes>:int},R:type{_()<computes>:int})<computes>:type{_()<computes>:int}=block{Ignored:=G();R}\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=F\n    set Stored=Observe(Dummy,F)\n    Sleep(0.001)\n    F()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", false, "result 11\n"),
  ("saved-alias", "One()<computes>:int=11\nTwo()<computes>:int=22\nRead(V:type{_()<computes>:int})<computes>:int=V()\nObserve(G:type{_()<computes>:int},R:type{_()<computes>:int})<computes>:type{_()<computes>:int}=block{Ignored:=G();R}\nbox(t:type):=class<computes>{A:t}\nCaller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n    var Stored:type{_()<computes>:int}=Dummy\n    Saved:=Stored\n    set Stored=F\n    Sleep(0.001)\n    Saved()\nMain()<suspends>:void=Print(\"result {Caller(One,Two)}\")\n", false, "result 22\n")
 ]

-- The logical provenance view can omit physical lowering accesses. These
-- pre-lowering models require actual exports/reads and forwarded/local aliases
-- to retain the original shared-write boundary, independently of source syntax.
private def ownership : IO Unit := do
  let logical : Expr := .seq (.assign 2 (.local 0)) (.seq (.assign 2 (.local 1)) (.lit (.int 1)))
  for dummy in [false,true] do
    for kind in ["private", "physical-export", "physical-read", "forwarded", "own-alias", "own-alias-type-view"] do
      let physical := if kind == "physical-export" then .seq FrameRefs.current logical
        else if kind == "physical-read" then .seq logical (.local 2) else logical
      let alias := kind == "own-alias" || kind == "own-alias-type-view"
      let ownLogical := if alias then .seq (.assign 3 (.local 0)) (.seq logical (.local 3)) else logical
      let physical := if alias then ownLogical else physical
      let caller : Fn := { name := "Caller", arity := 2, nslots := 4, decides := false, body := physical }
      let other : Fn := { name := "Bridge", arity := 0, nslots := 0, decides := false, body := .lit .void }
      let origin : FrameRefs.Origin := {frame := "Caller", name := "Stored", args := []}
      let ci : MetadataFlow.Info := {
        inputs := if dummy then [1] else [], shared := [2],
        source := {explicit := 2, slots := [(2,origin)] ++
          (if alias then [(3,{origin with args := if kind == "own-alias-type-view" then [.int] else []})] else [])},
        body := some ownLogical }
      let oi : MetadataFlow.Info := {
        source := {forwarded := if kind == "forwarded" then [origin] else []}, body := some (.lit .void) }
      let expected := !dummy || kind == "private"
      match MetadataFlow.check #[caller,other] #[ci,oi] #[] with
      | .ok _ => unless expected do throw <| IO.userError s!"{kind}/{dummy}: unsafe admission"
      | .error message =>
        if expected || !(message.splitOn "dummy type value cannot").length > 1 then
          throw <| IO.userError s!"{kind}/{dummy}: unexpected refusal {message}"
  IO.println "private frame ownership models passed (12 classifications)"

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
  if args == ["--ownership"] then
    ownership
    return
  let some index := args[0]?.bind String.toNat? | throw <| IO.userError "expected case index"
  let some (name, source, accepted, output) := cases[index]? | throw <| IO.userError "invalid case index"
  let some path := (args[1]? : Option String) | throw <| IO.userError "expected artifact directory"
  for extended in [false,true] do
    for dummy in [false,true] do
      match compile source dummy extended with
      | .ok c =>
        unless !dummy || accepted do throw <| IO.userError s!"{name}: unexpectedly admitted metadata"
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
  IO.println s!"private metadata store case passed: {name}"
