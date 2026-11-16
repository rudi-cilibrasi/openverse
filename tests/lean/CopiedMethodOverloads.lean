import OpenVerse.Front.Elab
open OpenVerse OpenVerse.Front

/- The typed two-loop form independently fixes each overload list.
   Real callables remain executable; metadata callables may be forwarded
   or ignored, but cannot become receivers in either copied list. -/
private def source (copied recursive execute : Bool) (argument : String) : String :=
  let consume := if execute then "V()" else "1"
  let body := if recursive then "if(K=0)then V else(M(V,K-1)|V)" else "V|V"
  "One()<computes>:int=1\n" ++
  "Keep()<computes>:type{_()<computes>:int}=One\n" ++
  "a:=class<computes>:\n" ++
  "    M(V:type{_()<computes>:int},K:int)<computes>:type{_()<computes>:int}=" ++ body ++ "\n" ++
  "    M(S:string)<computes>:type{_()<computes>:int}=Keep()|Keep()\n" ++
  "Dup(V:t where t:type)<computes>:t=V|V\n" ++
  "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n" ++
  (if copied then
    "    Rows:=for(A:=Dup((" ++ argument ++ ",1))|Dup(\"s\"),V:=a{}.M(A)):" ++ consume ++ "\n    Rows.Length\n"
   else
    "    Left:=for(A:=Dup((" ++ argument ++ ",1)),V:=a{}.M(A)):" ++ consume ++ "\n" ++
    "    Right:=for(A:=Dup(\"s\"),V:=a{}.M(A)):" ++ consume ++ "\n    Left.Length+Right.Length\n") ++
  "Main():void={}\n"

def main : IO Unit := do
  let variants := [false,true]
  let mut count := 0
  for copied in variants do
    for recursive in [false,true] do
      for execute in [false,true] do
        for argument in ["F","Dummy"] do
          for dummy in [false,true] do
            let result := do
              let tops ← parseProgram (source copied recursive execute argument)
              elabProgram (tops.map fun (top : STop) => match top with
                | .fn p n ps ts fx ret body => .fn p n (ps.map fun (parameter : SParam) =>
                  { parameter with typeValue := dummy && n == "Caller" && parameter.name == "Dummy" }) ts fx ret body
                | top => top)
            let reject := dummy && execute && argument == "Dummy"
            let label := s!"copied={copied} recursive={recursive} execute={execute} argument={argument} dummy={dummy}"
            match result with
            | .ok compiled =>
              unless !reject && compiled.prog.check && compiled.prog.checkControl &&
                  compiled.prog.checkTypes compiled.sigs compiled.slotTys do
                throw <| IO.userError s!"{label}: unexpected admission or invalid Core"
            | .error error =>
              if !reject || (error.splitOn "dummy type value cannot").length ≤ 1 then
                throw <| IO.userError s!"{label}: {error}"
            count := count+1
  IO.println s!"copied method callable metadata contracts passed ({count} checked variants)"
