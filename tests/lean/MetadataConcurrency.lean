import OpenVerse.Front.Elab

open OpenVerse OpenVerse.Front

private def functionTy := "type{_()<computes>:int}"
private def header (ret : String := "int") : String :=
  s!"Caller(F:{functionTy},Dummy:{functionTy})<suspends>:{ret}=\n"
private def result (kind : String) := if kind == "sync" then "Values(2)" else "Values"

private def readerCaller (body : String) : String :=
  "reader:=class<computes>{N:int=7}\nCaller(F:reader,Dummy:reader)<suspends>:reader=\n" ++ body

private def refusals (kind : String) : List (String × String × Bool) := [
  (s!"{kind}: cyclic shared modes reject invalid metadata writes", readerCaller
    s!"    var X:reader=Dummy\n    var Y:reader=F\n    V:={kind}:\n        block:\n            Sleep(0.1)\n            set X=Y\n            0\n        block:\n            Sleep(0.1)\n            set Y=Dummy\n            set X=Dummy\n            0\n    X", false),
  (s!"{kind}: metadata writer before sibling real writer", header ++
    s!"    var Stored:{functionTy}=Dummy\n    Values:={kind}:\n        block:\n            Sleep(0.1)\n            set Stored=Dummy\n            Sleep(0.5)\n            0\n        block:\n            set Stored=F\n            Sleep(0.5)\n            0\n        block:\n            Sleep(0.2)\n            Stored()\n    {result kind}", true),
  (s!"{kind}: reader before sibling real overwrite", header ++
    s!"    var Stored:{functionTy}=Dummy\n    Values:={kind}:\n        block:\n            Sleep(0.2)\n            set Stored=F\n            0\n        block:\n            Sleep(0.3)\n            0\n        block:\n            Sleep(0.1)\n            Stored()\n    {result kind}", true),
  (s!"{kind}: nonreturning sibling does not hide writes", header ++
    s!"    var Stored:{functionTy}=F\n    Values:={kind}:\n        block:\n            Sleep(0.1)\n            loop:\n                Sleep(1.0)\n        block:\n            Sleep(0.1)\n            set Stored=Dummy\n            0\n        block:\n            Sleep(0.2)\n            Stored()\n    {result kind}", true),
  (s!"{kind}: dispatch error does not hide sibling writes", header ++
    s!"    var Stored:{functionTy}=Dummy\n    set Stored=F\n    Values:={kind}:\n        block:\n            Sleep(0.2)\n            Stored()\n        block:\n            Sleep(0.1)\n            set Stored=Dummy\n            0\n        block:\n            Sleep(0.3)\n            0\n    {result kind}", false)]

private def forwards (kind : String) : List (String × String × Bool) := [
  (s!"{kind}: cyclic metadata-only forwarding converges", readerCaller
    s!"    var X:reader=Dummy\n    var Y:reader=Dummy\n    V:={kind}:\n        block:\n            Sleep(0.1)\n            set X=Y\n            0\n        block:\n            Sleep(0.1)\n            set Y=X\n            0\n    X", false),
  (s!"{kind}: metadata-only shared forwarding", header functionTy ++
    s!"    var Stored:{functionTy}=Dummy\n    Values:={kind}:\n        block:\n            Sleep(0.1)\n            set Stored=Dummy\n        block:\n            Sleep(0.2)\n            set Stored=Dummy\n        block:\n            Sleep(0.3)\n            Stored\n    Stored", true),
  (s!"{kind}: all arms overwrite with real data", header ++
    s!"    var Stored:{functionTy}=Dummy\n    Values:={kind}:\n        block:\n            set Stored=F\n            Sleep(0.1)\n            0\n        block:\n            set Stored=F\n            Sleep(0.2)\n            0\n        block:\n            set Stored=F\n            Sleep(0.3)\n            0\n    Stored()", true),
  (s!"{kind}: independent arm locals", header ++
    s!"    Values:={kind}:\n        block:\n            var A:{functionTy}=Dummy\n            set A=F\n            Sleep(0.1)\n            A()\n        block:\n            var B:{functionTy}=Dummy\n            set B=F\n            Sleep(0.2)\n            B()\n        block:\n            var C:{functionTy}=Dummy\n            set C=F\n            Sleep(0.3)\n            C()\n    {result kind}", true)]

private def extras : List (String × String × Bool) := [
  ("race: cleanup sees argument effects before the wait", header ++
    s!"    var Stored:{functionTy}=Dummy\n    race:\n        block:\n            defer:\n                Value:=Stored()\n            loop:\n                Sleep(block\{set Stored=F;1.0})\n        block:\n            Sleep(0.1)\n            0", true),
  ("race: real cleanup alias is independent of metadata cell", header ++
    s!"    var Stored:{functionTy}=Dummy\n    Saved:=F\n    race:\n        block:\n            defer:\n                Value:=Saved()\n            loop:\n                Sleep(1.0)\n        block:\n            Sleep(0.1)\n            0", true),
  ("race: cleanup forwards metadata opaquely", header ++
    s!"    var Stored:{functionTy}=Dummy\n    race:\n        block:\n            defer:\n                Saved:=Stored\n            loop:\n                Sleep(1.0)\n        block:\n            Sleep(0.1)\n            0", true),
  ("race: nonwaiting call cannot run cancellation cleanup", "NoWait()<suspends>:void={}\n" ++ header ++
    s!"    var Stored:{functionTy}=Dummy\n    race:\n        block:\n            defer:\n                Value:=Stored()\n            loop:\n                NoWait()\n        block:\n            Sleep(0.1)\n            0", true),
  ("race: zero sleep cannot run cancellation cleanup", header ++
    s!"    var Stored:{functionTy}=Dummy\n    race:\n        block:\n            defer:\n                Value:=Stored()\n            loop:\n                Sleep(0.0)\n        block:\n            Sleep(0.1)\n            0", true),
  ("branch: opaque metadata-only forwarding", header functionTy ++
      s!"    var Stored:{functionTy}=Dummy\n    branch:\n        Sleep(0.1)\n        set Stored=Dummy\n    Sleep(0.2)\n    Stored", true),
    ("branch: immediate metadata writer completes before real overwrite", header ++
      s!"    var Stored:{functionTy}=Dummy\n    branch:\n        set Stored=Dummy\n    set Stored=F\n    Stored()", true),
    ("branch: real overwrite before its first wait", header ++
      s!"    var Stored:{functionTy}=Dummy\n    branch:\n        set Stored=F\n        Sleep(0.1)\n    Sleep(0.2)\n    Stored()", true),
    ("branch: mutually exclusive real overwrite", ((header functionTy).replace "Caller(" "Caller(C:logic,") ++
      s!"    var Stored:{functionTy}=Dummy\n    if(C?)then:\n        branch:\n            Sleep(0.1)\n            set Stored=Dummy\n    else:\n        set Stored=F\n    Sleep(0.2)\n    Stored", true),
    ("branch: parent real overwrite rolls back", header functionTy ++
      s!"    var Stored:{functionTy}=Dummy\n    branch:\n        Sleep(0.1)\n        set Stored=Dummy\n    if(set Stored=F;false?)\{}\n    Sleep(0.2)\n    Stored", true),
    ("branch: pending metadata write canceled before it resumes", header ++
      s!"    var Stored:{functionTy}=Dummy\n    branch:\n        Sleep(0.1)\n        set Stored=Dummy\n    set Stored=F\n    Stored()", true),
    ("rush: loser canceled before it resumes", header ++
      s!"    var Stored:{functionTy}=Dummy\n    Value:=rush:\n        block:\n            Sleep(0.1)\n            set Stored=Dummy\n            Sleep(1.0)\n            0\n        block:\n            Sleep(0.05)\n            0\n    set Stored=F\n    Stored()", true),
  ("sync: same-arm metadata write precedes its real overwrite", header ++
    s!"    var Stored:{functionTy}=Dummy\n    Values:=sync:\n        block:\n            set Stored=Dummy\n            set Stored=F\n            Sleep(0.1)\n            0\n        block:\n            Sleep(0.2)\n            0\n    Stored()", true),
  ("sync: rolled-back sibling write has no effect", header ++
    s!"    var Stored:{functionTy}=Dummy\n    Values:=sync:\n        block:\n            set Stored=Dummy\n            set Stored=F\n            Sleep(0.1)\n            0\n        block:\n            if(set Stored=F;false?)\{}\n            Sleep(0.2)\n            0\n    Stored()", true),
  ("sync: one definite real overwrite before continuation", header ++
    s!"    var Stored:{functionTy}=Dummy\n    Values:=sync:\n        block:\n            Sleep(0.1)\n            set Stored=F\n            0\n        block:\n            Sleep(0.2)\n            0\n    Stored()", true)]

private def backgroundRefusals : List (String × String × Bool) := [
  ("branch: nonreturning background child does not hide owner return",
    "Finish()<suspends>:void=\n    branch:\n        loop:\n            Sleep(1.0)\n" ++ header ++
    "    spawn{Finish()}\n    Dummy()", true),
  ("race: cleanup alias survives real cell overwrite", header ++
    s!"    var Stored:{functionTy}=Dummy\n    Saved:=Stored\n    race:\n        block:\n            defer:\n                Value:=Saved()\n            set Stored=F\n            loop:\n                Sleep(1.0)\n        block:\n            Sleep(0.1)\n            0", true),
  ("race: cancellation defer executes metadata", header ++
    s!"    var Stored:{functionTy}=Dummy\n    race:\n        block:\n            defer:\n                Value:=Stored()\n            loop:\n                Sleep(1.0)\n        block:\n            Sleep(0.1)\n            0", true),
  ("branch: later caller real overwrite", header ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        Sleep(0.1)\n        set Stored=Dummy\n    set Stored=F\n    Sleep(0.2)\n    Stored()", true),
  ("rush: loser writes after caller real overwrite", header ++
    s!"    var Stored:{functionTy}=Dummy\n    Value:=rush:\n        block:\n            Sleep(0.1)\n            set Stored=Dummy\n            Sleep(1.0)\n            0\n        block:\n            Sleep(0.05)\n            0\n    set Stored=F\n    Sleep(0.2)\n    Stored()", true),
  ("branch: caller reads before background real overwrite", header ++
    s!"    var Stored:{functionTy}=Dummy\n    branch:\n        Sleep(0.2)\n        set Stored=F\n    Sleep(0.1)\n    Stored()", true)]

private def compileCase (source : String) (dummy live : Bool) : Except String Compiled := do
  let implementations := if live then
    s!"One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:{functionTy}=if(C?)then One else Two\n" else ""
  let tops ← parseProgram (implementations ++ source ++ "\nMain():void={}")
  let tops := tops.map fun
    | .fn p name ps tps specs ret body => .fn p name (ps.map fun param =>
        { param with typeValue := dummy && name == "Caller" && param.name == "Dummy" }) tps specs ret body
    | top => top
  elabProgram tops

def main : IO Unit := do
  let kinds := ["sync", "race", "rush"]
  let cases := kinds.flatMap refusals ++ backgroundRefusals
  let controls := kinds.flatMap forwards ++ extras
  let mut failures := 0
  for (label, source, live) in cases ++ controls do
    for dummy in [false, true] do
      let shouldReject := dummy && cases.any (·.1 == label)
      match compileCase source dummy live with
      | .ok c =>
        if shouldReject || !(c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys) then
          IO.println s!"FAIL {label}, dummy={dummy}: admitted={shouldReject}, Core checks"
          failures := failures + 1
      | .error message =>
        if !shouldReject || (message.splitOn "dummy type value cannot").length ≤ 1 then
          IO.println s!"FAIL {label}, dummy={dummy}: {message}"
          failures := failures + 1
  if failures > 0 then throw (IO.userError s!"{failures} metadata concurrency contracts failed")
  IO.println s!"metadata concurrency contracts passed ({cases.length} real/dummy refusals, {controls.length} forwarding/overwrite pairs)"
