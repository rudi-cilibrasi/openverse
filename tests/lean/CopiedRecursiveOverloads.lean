import OpenVerse.Front.Elab
open OpenVerse OpenVerse.Front

/-- The explicit typed loops are an independent selection control. Both paths
    must retain the actual callable provenance through recursive frame data. -/
private def source (copied : Bool) (argument : String) : String :=
  let integer := if copied then "Values" else "IntValues"
  let string := if copied then "Values" else "StringValues"
  "One()<computes>:int=1\n" ++
  "Keep()<computes>:type{_()<computes>:int}=One\n" ++
  integer ++ "(V:t,K:int where t:type)<computes>:t=if(K=0)then V else(" ++ integer ++ "(V,K-1)|V)\n" ++
  string ++ "(S:string)<computes>:type{_()<computes>:int}=Keep()|Keep()\n" ++
  "Dup(V:t where t:type)<computes>:t=V|V\n" ++

  "Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=\n" ++
  (if copied then
    "    Rows:=for(A:=Dup((" ++ argument ++ ",1))|Dup(\"s\"),V:=Values(A)):V()\n    Rows.Length\n"
   else
    "    Left:=for(A:=Dup((" ++ argument ++ ",1)),V:=IntValues(A)):V()\n" ++
    "    Right:=for(A:=Dup(\"s\"),V:=StringValues(A)):V()\n    Left.Length+Right.Length\n") ++
  "Main():void={}\n"

def main : IO Unit := do
  for copied in [false, true] do
    for argument in ["F", "Dummy"] do
      for dummy in [false, true] do
        let result := do
          let tops ← parseProgram (source copied argument)
          elabProgram (tops.map fun (top : STop) => match top with
            | .fn p n ps ts fx ret body => .fn p n (ps.map fun (parameter : SParam) =>
              { parameter with typeValue := dummy && n == "Caller" && parameter.name == "Dummy" }) ts fx ret body
            | top => top)
        let reject := dummy && argument == "Dummy"
        match result with
        | .ok compiled =>
          if reject || !(compiled.prog.check && compiled.prog.checkControl &&
              compiled.prog.checkTypes compiled.sigs compiled.slotTys) then
            throw (IO.userError s!"copied recursive evidence copied={copied} argument={argument} dummy={dummy}: admitted or invalid Core")
        | .error error =>
          if !reject || (error.splitOn "dummy type value cannot").length ≤ 1 then
            throw (IO.userError s!"copied recursive evidence copied={copied} argument={argument} dummy={dummy}: {error}")
  IO.println "copied recursive overload metadata contracts passed (typed controls and actual executable evidence)"
