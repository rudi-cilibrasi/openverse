/- Metadata contracts for a map's lookups, the primitives mapGet and mapFind (#795).
   A lookup is modelled as an index at an unknown position followed by the pair's second column.
   Three parts, each of which fails when its part of the model is removed:
   `Pairs`: source programs in which a dummy type value stored in a map is executed (refused) or
   not (controls), the role of a lookup's value; `Cells`: compiler-private cells as a map's
   values, the cell references of a lookup's value (`MetadataFlow`); `References`: object
   references through a lookup and the events a function may signal (`MetadataReferences`). -/
import OpenVerse.Front.Elab
import OpenVerse.Front.MetadataFlow

namespace MetadataMaps.Pairs
open OpenVerse OpenVerse.Front

/-- `Caller`'s parameter `Dummy` is metadata when `dummy`. -/
private partial def roles (dummy : Bool) : STop → Except String STop
  | .fn p name ps tps specs ret body =>
    pure (.fn p name (ps.map fun param =>
      { param with typeValue := dummy && name == "Caller" && param.name == "Dummy" }) tps specs ret body)
  | top => pure top

private def pre : String :=
  "One()<computes>:int=1\nTwo()<computes>:int=2\nfn:=type{_()<computes>:int}\n" ++
  "box:=struct{N:int,G:type{_()<computes>:int}}\ncell:=class{var G:type{_()<computes>:int}}\nholder:=struct{C:cell}\n"

private def caller (body : String) : String :=
  pre ++ "Poke(C:cell,H:type{_()<computes>:int})<transacts>:void=\n    set C.G=H\n" ++ "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n" ++ body ++
  "\nMain():void=\n    Print(\"{Caller(One,Two)}\")\n"

/-- label, body, whether the dummy is executed (so a dummy must be refused) -/
private def cases : List (String × String × Bool) := [
  ("literal map, lookup, call", "    M:[int]type{_()<computes>:int}=map{1=>Dummy}\n    if(G:=M[1])then G() else 0", true),
  ("literal map of two, lookup the dummy's key", "    M:[int]type{_()<computes>:int}=map{1=>F,2=>Dummy}\n    if(G:=M[2])then G() else 0", true),
  ("literal map of two, lookup by a computed key", "    M:[int]type{_()<computes>:int}=map{1=>F,2=>Dummy}\n    K:=F()+1\n    if(G:=M[K])then G() else 0", true),
  ("set an existing key to the dummy, lookup, call", "    var M:[int]type{_()<computes>:int}=map{1=>F}\n    if(set M[1]=Dummy){}\n    if(G:=M[1])then G() else 0", true),
  ("set a new key to the dummy, lookup, call", "    var M:[int]type{_()<computes>:int}=map{1=>F}\n    if(set M[2]=Dummy){}\n    if(G:=M[2])then G() else 0", true),
  ("string keys", "    var M:[string]type{_()<computes>:int}=map{\"a\"=>F}\n    if(set M[\"b\"]=Dummy){}\n    if(G:=M[\"b\"])then G() else 0", true),
  ("tuple value holding the dummy", "    M:[int]tuple(int,type{_()<computes>:int})=map{1=>(5,Dummy)}\n    if(P:=M[1])then P(1)() else 0", true),
  ("option value holding the dummy", "    M:[int]?type{_()<computes>:int}=map{1=>option{Dummy}}\n    if(O:=M[1],G:=O?)then G() else 0", true),
  ("struct value holding the dummy", "    M:[int]box=map{1=>box{N:=1,G:=Dummy}}\n    if(B:=M[1])then B.G() else 0", true),
  ("array value holding the dummy", "    M:[int][]type{_()<computes>:int}=map{1=>array{F,Dummy}}\n    if(A:=M[1],G:=A[1])then G() else 0", true),
  ("nested map", "    M:[int][int]type{_()<computes>:int}=map{1=>map{2=>Dummy}}\n    if(G:=M[1][2])then G() else 0", true),
  ("map in an array", "    A:[][int]type{_()<computes>:int}=array{map{1=>Dummy}}\n    if(M:=A[0],G:=M[1])then G() else 0", true),
  ("lookup inside a loop", "    M:[int]type{_()<computes>:int}=map{1=>F,2=>Dummy}\n    var S:int=0\n    for(K:=1..2):\n        if(G:=M[K])then set S+=G()\n    S", true),
  ("lookup, store in a var, call later", "    M:[int]type{_()<computes>:int}=map{1=>Dummy}\n    var H:type{_()<computes>:int}=F\n    if(G:=M[1])then set H=G\n    H()", true),
  ("lookup, put in another map, lookup, call", "    M:[int]type{_()<computes>:int}=map{1=>Dummy}\n    var N:[int]type{_()<computes>:int}=map{}\n    if(G:=M[1],set N[7]=G){}\n    if(H:=N[7])then H() else 0", true),
  ("ConcatenateMaps, lookup, call", "    M:[int]type{_()<computes>:int}=ConcatenateMaps(map{1=>F},map{2=>Dummy})\n    if(G:=M[2])then G() else 0", true),
  ("lookup with or default, call", "    M:[int]type{_()<computes>:int}=map{1=>Dummy}\n    G:=M[1] or F\n    G()", true),
  ("lookup in a not, then iterate and call", "    M:[int]type{_()<computes>:int}=map{1=>Dummy}\n    var S:int=0\n    if(not M[9]):\n        for(K->G:M){set S+=G()}\n    S", true),
  -- objects reached through a map: a write or a read through the looked-up reference
  ("object in a map, dummy written through the lookup, called through the original", "    O:=cell{G:=F}\n    M:[int]cell=map{1=>O}\n    if(C:=M[1])then set C.G=Dummy\n    O.G()", true),
  ("object in a map, dummy written through the original, called through the lookup", "    O:=cell{G:=F}\n    M:[int]cell=map{1=>O}\n    set O.G=Dummy\n    if(C:=M[1])then C.G() else 0", true),
  ("object holding the dummy in a map, called through the lookup", "    M:[int]cell=map{1=>cell{G:=Dummy}}\n    if(C:=M[1])then C.G() else 0", true),
  ("two lookups of one object, written through one, called through the other", "    M:[int]cell=map{1=>cell{G:=F}}\n    if(C:=M[1])then set C.G=Dummy\n    if(D:=M[1])then D.G() else 0", true),
  ("object in a tuple value, written through the lookup", "    O:=cell{G:=F}\n    M:[int]tuple(int,cell)=map{1=>(0,O)}\n    if(P:=M[1])then set P(1).G=Dummy\n    O.G()", true),
  ("object in a struct value, written through the lookup", "    O:=cell{G:=F}\n    M:[int]holder=map{1=>holder{C:=O}}\n    if(H:=M[1])then set H.C.G=Dummy\n    O.G()", true),
  ("object in an array value, written through the lookup", "    O:=cell{G:=F}\n    M:[int][]cell=map{1=>array{O}}\n    if(A:=M[1],C:=A[0])then set C.G=Dummy\n    O.G()", true),
  ("object in a nested map, written through the lookup", "    O:=cell{G:=F}\n    M:[int][int]cell=map{1=>map{2=>O}}\n    if(C:=M[1][2])then set C.G=Dummy\n    O.G()", true),
  ("object put by set, written through the lookup", "    O:=cell{G:=F}\n    var M:[int]cell=map{}\n    if(set M[3]=O){}\n    if(C:=M[3])then set C.G=Dummy\n    O.G()", true),
  ("object as a key's value among others, written through a computed lookup", "    O:=cell{G:=F}\n    Q:=cell{G:=F}\n    M:[int]cell=map{1=>Q,2=>O}\n    K:=F()+1\n    if(C:=M[K])then set C.G=Dummy\n    O.G()", true),
  ("object passed to a helper through a lookup", "    O:=cell{G:=F}\n    M:[int]cell=map{1=>O}\n    if(C:=M[1])then Poke(C,Dummy)\n    O.G()", true),
  ("object in a map, real written through the lookup, called (control)", "    O:=cell{G:=F}\n    M:[int]cell=map{1=>O}\n    if(C:=M[1])then set C.G=F\n    D:=Dummy\n    O.G()", false),
  ("another object written through the lookup (control)", "    O:=cell{G:=F}\n    Q:=cell{G:=F}\n    M:[int]cell=map{1=>Q}\n    if(C:=M[1])then set C.G=Dummy\n    O.G()", false),
  -- the dummy is stored and never executed
  ("dummy stored, never looked up", "    M:[int]type{_()<computes>:int}=map{1=>Dummy}\n    M.Length", false),
  ("dummy stored, looked up, not called", "    M:[int]type{_()<computes>:int}=map{1=>Dummy}\n    if(G:=M[1])then 1 else 0", false),
  ("two maps, only the real one's value called", "    M:[int]type{_()<computes>:int}=map{1=>F}\n    N:[int]type{_()<computes>:int}=map{1=>Dummy}\n    if(G:=M[1])then G()+N.Length else 0", false),
  ("int map beside the dummy", "    M:[int]int=map{1=>10}\n    D:=Dummy\n    if(V:=M[1])then V+F() else 0", false),
  ("dummy overwritten by the real one before the lookup", "    var M:[int]type{_()<computes>:int}=map{1=>Dummy}\n    if(set M[1]=F){}\n    if(G:=M[1])then G() else 0", false)]

private def suspending (body : String) : String :=
  pre ++ "Waiter(E:event(type{_()<computes>:int}))<suspends>:void=\n    G:=E.Await()\n    Print(\"{G()}\")\n" ++
  "Relay(E:event(type{_()<computes>:int}),H:type{_()<computes>:int}):void=\n    E.Signal(H)\n" ++
  "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=\n" ++ body ++
  "\nMain()<suspends>:void=\n    V:=Caller(One,Two)\n    Print(\"{V}\")\n"

private def eventCases : List (String × String × Bool) := [
  ("event in a map, dummy signalled through the lookup, awaited on the original", "    E:=event(type{_()<computes>:int}){}\n    M:[int]event(type{_()<computes>:int})=map{1=>E}\n    spawn{Waiter(E)}\n    Sleep(0.0)\n    if(X:=M[1])then X.Signal(Dummy)\n    Sleep(0.0)\n    0", true),
  ("event in a map, dummy signalled on the original, awaited through the lookup", "    E:=event(type{_()<computes>:int}){}\n    M:[int]event(type{_()<computes>:int})=map{1=>E}\n    if(X:=M[1])then spawn{Waiter(X)}\n    Sleep(0.0)\n    E.Signal(Dummy)\n    Sleep(0.0)\n    0", true),
  ("event in a map of two, computed key, dummy signalled through the lookup", "    E:=event(type{_()<computes>:int}){}\n    Q:=event(type{_()<computes>:int}){}\n    M:[int]event(type{_()<computes>:int})=map{1=>Q,2=>E}\n    spawn{Waiter(E)}\n    Sleep(0.0)\n    K:=F()+1\n    if(X:=M[K])then X.Signal(Dummy)\n    Sleep(0.0)\n    0", true),
  ("event in a tuple value in a map, dummy signalled through the lookup", "    E:=event(type{_()<computes>:int}){}\n    M:[int]tuple(int,event(type{_()<computes>:int}))=map{1=>(0,E)}\n    spawn{Waiter(E)}\n    Sleep(0.0)\n    if(P:=M[1])then P(1).Signal(Dummy)\n    Sleep(0.0)\n    0", true),
  ("event looked up and passed to a helper that signals the dummy", "    E:=event(type{_()<computes>:int}){}\n    M:[int]event(type{_()<computes>:int})=map{1=>E}\n    spawn{Waiter(E)}\n    Sleep(0.0)\n    if(X:=M[1])then Relay(X,Dummy)\n    Sleep(0.0)\n    0", true),
  ("event put by set, dummy signalled through the lookup", "    E:=event(type{_()<computes>:int}){}\n    var M:[int]event(type{_()<computes>:int})=map{}\n    if(set M[4]=E){}\n    spawn{Waiter(E)}\n    Sleep(0.0)\n    if(X:=M[4])then X.Signal(Dummy)\n    Sleep(0.0)\n    0", true),
  ("awaiter runs the stored dummy when woken; event signalled through a map lookup", "    E:=event(int){}\n    M:[int]event(int)=map{1=>E}\n    var Stored:type{_()<computes>:int}=Dummy\n    branch:\n        E.Await()\n        Value:=Stored()\n    Sleep(0.0)\n    if(X:=M[1])then X.Signal(0)\n    Sleep(0.0)\n    0", true),
  ("awaiter runs the stored dummy when woken; event signalled through a lookup with a computed key", "    E:=event(int){}\n    Q:=event(int){}\n    M:[int]event(int)=map{1=>Q,2=>E}\n    var Stored:type{_()<computes>:int}=Dummy\n    branch:\n        E.Await()\n        Value:=Stored()\n    Sleep(0.0)\n    K:=F()+1\n    if(X:=M[K])then X.Signal(0)\n    Sleep(0.0)\n    0", true),
  ("awaiter runs the stored dummy when woken; event signalled directly (reference case)", "    E:=event(int){}\n    var Stored:type{_()<computes>:int}=Dummy\n    branch:\n        E.Await()\n        Value:=Stored()\n    Sleep(0.0)\n    E.Signal(0)\n    Sleep(0.0)\n    0", true),
  ("awaiter would run the stored dummy; nothing signals its event (control)", "    E:=event(int){}\n    M:[int]event(int)=map{1=>E}\n    var Stored:type{_()<computes>:int}=Dummy\n    branch:\n        E.Await()\n        Value:=Stored()\n    Sleep(0.0)\n    0", false),
  ("awaiter would run the stored dummy; another event is signalled through the lookup (control)", "    E:=event(int){}\n    Q:=event(int){}\n    M:[int]event(int)=map{1=>Q}\n    var Stored:type{_()<computes>:int}=Dummy\n    branch:\n        E.Await()\n        Value:=Stored()\n    Sleep(0.0)\n    if(X:=M[1])then X.Signal(0)\n    Sleep(0.0)\n    0", false),
  ("event in a map, real signalled through the lookup (control)", "    E:=event(type{_()<computes>:int}){}\n    M:[int]event(type{_()<computes>:int})=map{1=>E}\n    spawn{Waiter(E)}\n    Sleep(0.0)\n    D:=Dummy\n    if(X:=M[1])then X.Signal(F)\n    Sleep(0.0)\n    0", false),
  ("another event signalled with the dummy through the lookup, nobody awaits it (control)", "    E:=event(type{_()<computes>:int}){}\n    Q:=event(type{_()<computes>:int}){}\n    M:[int]event(type{_()<computes>:int})=map{1=>Q}\n    spawn{Waiter(E)}\n    Sleep(0.0)\n    if(X:=M[1])then X.Signal(Dummy)\n    E.Signal(F)\n    Sleep(0.0)\n    0", false)]

private def compileCase (source : String) (dummy : Bool) : Except String Compiled := do
  let tops ← parseProgram source
  elabProgram (← tops.mapM (roles dummy)) {}

def main : IO Unit := do
  let mut failures := 0
  let all := (cases.map fun (l, b, x) => (l, caller b, x)) ++ (eventCases.map fun (l, b, x) => (l, suspending b, x))
  for (label, source, executed) in all do
    match compileCase source false with
    | .ok c =>
      unless c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys do
        IO.println s!"FAIL {label}: the real program fails Core checks"; failures := failures + 1
    | .error m => IO.println s!"FAIL {label}: the real program is refused: {m}"; failures := failures + 1
    match compileCase source true with
    | .ok _ =>
      -- (a program that executes the dummy must be refused; one that does not may be either)
      if executed then
        IO.println s!"FAIL {label}: admitted with a dummy that it executes"; failures := failures + 1
    | .error m =>
      unless (m.splitOn "dummy type value").length > 1 do
        IO.println s!"FAIL {label}: refused for another reason: {m}"; failures := failures + 1
  if failures > 0 then throw (IO.userError s!"{failures} metadata map contracts failed")
  IO.println s!"metadata map contracts passed ({(all.filter (·.2.2)).length} programs that execute a dummy through a map refused, {(all.filter (!·.2.2)).length} controls)"
end MetadataMaps.Pairs

namespace MetadataMaps.Cells
open OpenVerse OpenVerse.Front

/-- A private cell (tag 0) holding slot 1, as a map's value: the pair `(key, cell)`. -/
private def cell (slot : Nat) : Expr := .heap (.new 0) [.local slot]
private def pair (k : Int) (v : Expr) : Expr := .prim .mkTup [.lit (.int k), v]

def main : IO Unit := do
  let mut bad := 0
  let mut n := 0
  for shape in ["literal", "appended", "updated", "nested"] do
    for keyKind in ["literal", "slot"] do
      let key := if keyKind == "literal" then Expr.lit (.int 7) else .local 2
      let map : Expr := match shape with
        | "literal" => .prim .mkArr [pair 5 (cell 1), pair 7 (cell 1)]
        | "appended" => .prim .concat [.prim .mkArr [pair 5 (cell 1)], .prim .mkArr [pair 7 (cell 1)]]
        | "updated" => .prim .arrSet [.prim .mkArr [pair 5 (cell 1), pair 7 (cell 1)], .lit (.int 1), pair 7 (cell 1)]
        | _ => .prim .mkArr [pair 5 (cell 1), pair 7 (cell 1)]
      -- the looked-up cell's content is executed
      let looked : Expr := if shape == "nested" then
          .heap (.get 0) [.prim .mapGet [.prim .mkArr [pair 1 (.prim .mapGet [.local 3, key])], .lit (.int 1)]]
        else .heap (.get 0) [.prim .mapGet [.local 3, key]]
      let fns : Array Fn := #[
        { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void },
        { name := "Caller", arity := 3, nslots := 4, decides := false,
          body := .seq (.assign 3 map) (.call 0 [looked]) }]
      for metadata in [false, true] do
        let infos : Array MetadataFlow.Info := fns.mapIdx fun i fn => {
          body := some fn.body
          cellTag := some 0
          required := if i == 0 then [0] else []
          inputs := if i == 1 && metadata then [1] else [] }
        let result := MetadataFlow.check fns infos #[[]]
        let admitted := match result with | .ok _ => true | .error _ => false
        n := n + 1
        if admitted != !metadata then
          bad := bad + 1
          IO.println s!"MISMATCH shape={shape} key={keyKind} metadata={metadata} admitted={admitted}"
  IO.println s!"map lookup cell carrier: {n} classifications; {bad} mismatches"
  if bad > 0 then throw <| IO.userError "map lookup cell carrier contract failed"
end MetadataMaps.Cells

namespace MetadataMaps.References
open OpenVerse OpenVerse.Front OpenVerse.Front.MetadataReferences

private def pair (k : Int) (v : Expr) : Expr := .prim .mkTup [.lit (.int k), v]

def main : IO Unit := do
  -- (1) references through a lookup: slot 0 holds object 2, slot 1 object 3
  let memory := initial 2 (fun i => [i+2])
  let objects := Expr.prim .mkArr [pair 5 (.local 0), pair 7 (.local 1)]
  let got := (eval #[] 1 memory (.prim .mapGet [objects, .lit (.int 7)])).1
  unless got.contains 2 && got.contains 3 do
    throw <| IO.userError s!"a lookup must give the references of the map's values, got {got}"
  let keyed := Expr.prim .mkArr [pair 5 (.lit (.int 1)), pair 7 (.lit (.int 2))]
  unless (eval #[] 2 memory (.prim .mapGet [keyed, .lit (.int 7)])).1.isEmpty do
    throw <| IO.userError "a lookup in a map of scalars gives no reference"
  unless (eval #[] 3 memory (.prim .mapFind [objects, .lit (.int 7)])).1.isEmpty do
    throw <| IO.userError "a key's position is an int: no reference"
  let appended := Expr.prim .concat [.prim .mkArr [pair 5 (.lit (.int 1))], .prim .mkArr [pair 7 (.local 1)]]
  unless ((eval #[] 4 memory (.prim .mapGet [appended, .local 0])).1).contains 3 do
    throw <| IO.userError "a lookup after an append must give the appended value's reference"
  let nested := Expr.prim .mkArr [pair 1 (.prim .mapGet [objects, .lit (.int 5)])]
  let through := (eval #[] 5 memory (.prim .mapGet [nested, .lit (.int 1)])).1
  unless through.contains 2 && through.contains 3 do
    throw <| IO.userError s!"a lookup of a looked-up value must keep its references, got {through}"
  -- (2) the events a function may signal: a map of events looked up, then signalled
  for update in [false, true] do
    let source := if update then
        "Send(Es:[int]event(int),K:int,Replacement:event(int),N:int)<transacts>:void=\n    if(N>0):\n        Send(Es,K,Replacement,N-1)\n    else:\n        var Updated:[int]event(int)=Es\n        if(set Updated[K]=Replacement){}\n        if(E:=Updated[K])then E.Signal(0)\n"
      else
        "Send(Es:[int]event(int),K:int,N:int)<transacts>:void=\n    if(N>0):\n        Send(Es,K,N-1)\n    else:\n        if(E:=Es[K])then E.Signal(0)\n"
    let c ← match (do let tops ← parseProgram (source ++ "\nMain():void={}"); elabProgram tops { signalNoRollback := false }) with
      | .ok c => pure c
      | .error m => throw (IO.userError s!"map Signal dependency control failed to compile: {m}")
    unless c.prog.check && c.prog.checkControl && c.prog.checkTypes c.sigs c.slotTys do
      throw (IO.userError "map Signal dependency control failed Core checks")
    let fns := c.prog.fns.toArray
    let some index := fns.findIdx? (·.name == "Send") | throw (IO.userError "lost Send")
    -- (with the update, the key is in the stored pair, so it is a dependency too; the
    -- interpreted loops this primitive replaced gave the same lists)
    let expected := if update then [0, 1, 2] else [0]
    let actual := (signalArguments fns)[index]!
    unless actual == expected do
      throw (IO.userError s!"update={update}: wrong Signal dependencies through a map lookup: {actual}, expected {expected}")
  IO.println "map lookup reference contracts passed (values' references, scalars, positions, append, nested; Signal dependencies of a looked-up event, with and without an update)"
end MetadataMaps.References

def main : IO Unit := do
  MetadataMaps.Pairs.main
  MetadataMaps.Cells.main
  MetadataMaps.References.main
