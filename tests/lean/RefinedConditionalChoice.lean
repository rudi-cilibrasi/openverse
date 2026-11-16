import OpenVerse.Front.Elab
import OpenVerse.Core.Bounded
import OpenVerse.Core.Encode

open OpenVerse OpenVerse.Front

private def callable := "type{_()<computes>:int}"
private def sourcePrefix := "expr(t:type) := class<abstract>:\n    Eval():t\nlit := class(expr(int)):\n    V:int\n    Eval<override>():int = V\nvpair(a:type, b:type) := class(expr(tuple(a, b))):\n    var L:expr(a)\n    R:expr(b)\n    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())\n"
private def cases : List (String × String × String × String × Bool × Nat) := [
  ("real", "F()", "", "", true, 1),
  ("metadata", "Dummy()", "", "", false, 2),
  ("tuple-real", "Pair(1)()", "    Pair:=(Dummy,F)\n", "", true, 1),
  ("tuple-metadata", "Pair(0)()", "    Pair:=(Dummy,F)\n", "", false, 2),
  ("overwritten", "Stored()", "    var Stored:" ++ callable ++ "=Dummy\n", "set Stored=F,", true, 1),
  ("stored-metadata", "Stored()", "    var Stored:" ++ callable ++ "=Dummy\n", "", false, 2),
  ("waiting-real", "F()", "", "", true, 1),
  ("waiting-metadata", "Dummy()", "", "", false, 2),
  ("waiting-tuple-real", "Pair(1)()", "    Pair:=(Dummy,F)\n", "", true, 1),
  ("waiting-tuple-metadata", "Pair(0)()", "    Pair:=(Dummy,F)\n", "", false, 2),
  ("composed-real", "F()", "", "", true, 1),
  ("composed-metadata", "Dummy()", "", "", false, 2),
  ("waiting-composed-real", "F()", "", "", true, 1),
  ("waiting-composed-metadata", "Dummy()", "", "", false, 2)]

private def source (action locals condition : String) (waiting : Bool) : String :=
  let inner := action.startsWith "Pair"
  let branchLocals := if inner then "Pair:=(Dummy,F);" else ""
  let locals := if inner then "" else locals
  let code := "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:" ++ callable ++ "=if(C?)then One else Two\n" ++ sourcePrefix ++
  "Rows(E:expr(t),F:" ++ callable ++ ",Dummy:" ++ callable ++ " where t:type):[]t=\n" ++ locals ++
  "    for(N:=1..2,V:=if(Print(\"prefix\")," ++ condition ++ "P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then{" ++ branchLocals ++ "((L.V+" ++ action ++ ",R.V)|(L.V+1+" ++ action ++ ",R.V))}else E.Eval()){V}\n" ++
  "Main():void=\n    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}\n    Values:=Rows(P,One,Two)\n    for(V:Values){Print(\"{V(0)} {V(1)}\")}\n    Print(\"final {P.L.Eval()}\")\n"
  if waiting then code.replace " where t:type):[]t" " where t:type)<suspends>:[]t"
    |>.replace "){V}\n" "){Sleep(0.001);V}\n"
    |>.replace "Main():void" "Main()<suspends>:void"
  else code


private def composedSource (action : String) (waiting : Bool) : String :=
  let code := "One()<computes>:int=1\nTwo()<computes>:int=2\nPick(C:logic)<computes>:" ++ callable ++ "=if(C?)then One else Two\n" ++ sourcePrefix ++
    "Rows(E:expr(t),Other:expr(u),F:" ++ callable ++ ",Dummy:" ++ callable ++ " where t:type,u:type):[]tuple(t,u)=\n" ++
    "    for(N:=1..2,V:=if(Print(\"prefix\"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then((L.V,R.V)|(L.V+1,R.V))else E.Eval()," ++
    "W:=if(Print(\"second\"),Q:=vpair[Other],SavedQ:=Q.L,LQ:=lit[SavedQ],set Q.L=lit{V:=99},RQ:=lit[Q.R])then((LQ.V+" ++ action ++ ",RQ.V)|(LQ.V+1+" ++ action ++ ",RQ.V))else Other.Eval()){(V,W)}\n" ++
    "Main():void=\n    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}\n    Q:=vpair(int,int){L:=lit{V:=5},R:=lit{V:=9}}\n    Values:=Rows(P,Q,One,Two)\n    for(V:Values){Print(\"{V(0)(0)} {V(0)(1)} {V(1)(0)} {V(1)(1)}\")}\n    Print(\"final {P.L.Eval()} {Q.L.Eval()}\")\n"
  if waiting then code.replace "):[]" ")<suspends>:[]"
    |>.replace "){(V,W)}\n" "){Sleep(0.001);(V,W)}\n"
    |>.replace "Main():void" "Main()<suspends>:void"
  else code

private def composedTrace (value : Nat) : String :=
  "prefix\nsecond\nsecond\nprefix\nsecond\nsecond\n" ++
    s!"3 7 {5+value} 9\n3 7 {6+value} 9\n4 7 {99+value} 9\n4 7 {100+value} 9\n" ++
    s!"99 7 {99+value} 9\n99 7 {100+value} 9\n100 7 {99+value} 9\n100 7 {100+value} 9\nfinal 99 99\n"

private def compile (source : String) (dummy inferred : Bool) : Except String Compiled := do
  let tops ← parseProgram source
  elabProgram (tops.map fun
    | .fn p name ps tps fx result body =>
      let wrap := fun value => [.decl value.pos "Inferred" none false value, .ident value.pos "Inferred"]
      let body := if !inferred || name != "Rows" then body else match body with
        | value@(.forE p ..) => .block p (wrap value)
        | .block p expressions => match expressions.getLast? with
          | some value@(.forE ..) => .block p (expressions.dropLast ++ wrap value)
          | _ => body
        | _ => body
      .fn p name (ps.map fun parameter =>
        { parameter with typeValue := dummy && name == "Rows" && parameter.name == "Dummy" }) tps fx result body
    | top => top)

/-- The normal collector path has bottom element type. Executable evidence
    in a callable tuple still crosses the source return cell precisely. -/
private def returnCellCases (directory : String) : IO Unit := do
  let source : String := "One()<computes>:int=1\nTwo()<computes>:int=2\nexpr(t:type) := class<abstract>:\n    Eval():t\nlit := class(expr(int)):\n    V:int\n    Eval<override>():int = V\nvpair(a:type, b:type) := class(expr(tuple(a, b))):\n    var L:expr(a)\n    R:expr(b)\n    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())\nRows(E:expr(t),F:type{_()<computes>:int},Dummy:type{_()<computes>:int} where t:type):tuple(type{_()<computes>:int},t)=\n    for(N:=1..2,V:=if(Print(\"prefix\"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then((L.V,R.V)|(L.V+1,R.V))else E.Eval()){return(ACTION,V)}\n    (F,E.Eval())\nMain():void=\n    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}\n    Value:=Rows(P,One,Two)\n    Print(\"{Value(0)()} {Value(1)(0)} {Value(1)(1)}\")\n    Print(\"final {P.L.Eval()}\")\n"
  for waiting in [false,true] do
    let source := if waiting then source.replace " where t:type):tuple" " where t:type)<suspends>:tuple"
      |>.replace "){return(" "){Sleep(0.001);return("
      |>.replace "Main():void" "Main()<suspends>:void" else source
    for (action, value) in [("F",1),("Dummy",2)] do
      for dummy in [false,true] do
        match compile (source.replace "ACTION" action) dummy false with
        | .error message =>
          unless dummy && action == "Dummy" && (message.splitOn "dummy type value cannot").length > 1 do
            throw <| IO.userError s!"returncell/{action}/{dummy}: {message}"
        | .ok compiled =>
          if dummy && action == "Dummy" then throw <| IO.userError "dummy callable returncell admitted"
          unless compiled.prog.check && compiled.prog.checkControl &&
              compiled.prog.checkTypes compiled.sigs compiled.slotTys do
            throw <| IO.userError "returncell: invalid Core"
          let expected := s!"prefix\n{value} 3 7\nfinal 99\n"
          match compiled.prog.runB 10000000 10000 with
          | .res (.ok _, output) =>
            unless String.ofList (output.map Char.ofNat) == expected do
              throw <| IO.userError "returncell: wrong complete trace"
          | _ => throw <| IO.userError "returncell: VM did not complete"
          let path := s!"{directory}/returncell-{waiting}-{action}-{dummy}"
          IO.FS.writeBinFile (path ++ ".vbc") compiled.prog.encode
          IO.FS.writeFile (path ++ ".expected") expected
  IO.println "callable source returncell contracts passed (4 real/metadata pairs)"

/-- Internal firstDecides collection adds its singleton even with no source
    prefix; the ordinary empty-prefix path does not. Both retain []t bodies. -/
private def shapeModes (directory : String) : IO Unit := do
  let source ← IO.FS.readFile "tests/verse/class_cast_refine_conditional_choice_nested_no_prefix.verse"
  let expected := "prefix\n3 7\n3 7\n4 7\n4 7\nfinal 99\n"
  for first in [false,true] do
    let tops ← match parseProgram source with
      | .ok tops => pure tops
      | .error message => throw <| IO.userError message
    let tops := if !first then tops else tops.map fun
      | .fn p name ps tps fx result (.forE q clauses body) =>
        if name != "Rows" then .fn p name ps tps fx result (.forE q clauses body) else
        .fn p name ps tps fx result (.app q (.ident q "$refinementContinue")
          [.decl q "$value" (some (.arr (.name "t"))) false (.tuple q []),
           .app q (.ident q "$forFirst") [.block q clauses, body] false] false)
      | top => top
    let compiled ← match elabProgram tops with
      | .ok compiled => pure compiled
      | .error message => throw <| IO.userError s!"shape/{first}: {message}"
    unless compiled.prog.check && compiled.prog.checkControl &&
        compiled.prog.checkTypes compiled.sigs compiled.slotTys do
      throw <| IO.userError s!"shape/{first}: invalid Core"
    match compiled.prog.runB 10000000 10000 with
    | .res (.ok _, output) =>
      unless String.ofList (output.map Char.ofNat) == expected do
        throw <| IO.userError s!"shape/{first}: wrong nested-array trace"
    | _ => throw <| IO.userError s!"shape/{first}: VM did not complete"
    let path := s!"{directory}/shape-{first}"
    IO.FS.writeBinFile (path ++ ".vbc") compiled.prog.encode
    IO.FS.writeFile (path ++ ".expected") expected
  IO.println "nested array modes passed (ordinary and firstDecides)"

def main (args : List String) : IO Unit := do
  let inferred := args.head? == some "--inferred"
  let args := if inferred then args.drop 1 else args
  if let ["--returns", directory] := args then
    returnCellCases directory
    return
  if let ["--shape", directory] := args then
    shapeModes directory
    return
  if args == ["--count"] then
    IO.println cases.length
    return
  let index ← match args.head?.bind String.toNat? with
    | some i => pure i
    | none => throw <| IO.userError "expected conditional metadata case index"
  let some (name, action, locals, condition, accepted, value) := cases[index]?
    | throw <| IO.userError "invalid conditional metadata case index"
  let composed := name.startsWith "composed" || name.startsWith "waiting-composed"
  let program := if composed then composedSource action (name.startsWith "waiting")
    else source action locals condition (name.startsWith "waiting")
  let expected := if composed then composedTrace value else s!"prefix\nprefix\n{3+value} 7\n{4+value} 7\n{99+value} 7\n{100+value} 7\nfinal 99\n"
  for dummy in [false,true] do
    match compile program dummy inferred with
    | .error message =>
      if !dummy || accepted || (message.splitOn "dummy type value cannot").length ≤ 1 then
        throw <| IO.userError s!"{name}/{dummy}: unexpected refusal {message}"
    | .ok compiled =>
      unless !dummy || accepted do throw <| IO.userError s!"{name}: metadata unexpectedly admitted"
      unless compiled.prog.check && compiled.prog.checkControl &&
          compiled.prog.checkTypes compiled.sigs compiled.slotTys do
        throw <| IO.userError s!"{name}/{dummy}: invalid Core"
      match compiled.prog.runB 10000000 10000 with
      | .res (.ok _, output) =>
        unless String.ofList (output.map Char.ofNat) == expected do
          throw <| IO.userError s!"{name}/{dummy}: wrong complete VM trace"
      | _ => throw <| IO.userError s!"{name}/{dummy}: VM exhaustion"
      if let some directory := args[1]? then
        let path := s!"{directory}/{if inferred then "inferred-" else ""}{name}-{dummy}"
        IO.FS.writeBinFile (path ++ ".vbc") compiled.prog.encode
        IO.FS.writeFile (path ++ ".expected") expected
  IO.println s!"conditional selected-world metadata pair passed: {name}"
