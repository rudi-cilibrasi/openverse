/- The recursive subtype coercions the metadata flow check does not replay (#721).
   A certified `$subtype….Up` gets its roles from its ordinary summary and an
   unknown result alias, with the caller's heap unchanged. These Core models
   are the cases that transfer must not admit: metadata in a private cell
   reached only through the coercion's result, metadata written through that
   result, and coercions named like the family whose bodies store into a
   cell, build one or read one, and so must keep their exact replay. Each has
   the control whose coercion has another name and is always replayed: the
   transfer may refuse more than the replay, never less.
   These are compiler API models with valid Core programs, not a claim that
   Source can pass a cell to a coercion.

   The Source pairs after them pass a real or a dummy value through each
   coercion Source can reach, inside the lazy loop helper that holds a
   captured `var`'s cell: the dummy is refused where the coerced value is
   executed, directly or after a round trip through the cell, and admitted
   where it is only kept. Every one of them took `openverse check` past its
   15 seconds before #721, apart from the three whose coercion is not a
   class's. -/
import OpenVerse

open OpenVerse OpenVerse.Front
namespace MetadataInertCoercions

-- Classes: 0 the private cell, 1 an executable carrier, 2 the dictionary
-- without a field, 3 the dictionary that holds another one.
private def callable : VTy := .ref [1] []
private def cell : VTy := .ref [0] [callable]
private def dictionary : VTy := .ref [2, 3] []
private def composed : VTy := .ref [3] []
private def carrier : VTy := .arr cell

private def first (carrier : Expr) : Expr := .prim .index [carrier, .lit (.int 0)]

/-- `Up(self, input, witness)`: the coercion of the dictionary in the
    receiver's field while that is a composed one, then what `shape` says. -/
private def coercion (shape : String) : Expr :=
  let inner : Expr := .heap (.isTag [3]) [.heap (.get 0) [.local 0]]
  let own := match shape with
    | "store" => Expr.seq (.heap (.set 0) [first (.local 1), .local 2]) (.local 1)
    | "build" => .prim .mkArr [.heap (.new 0) [.local 2]]
    | "read" => .seq (.call 0 [.heap (.get 0) [first (.local 1)]]) (.local 1)
    | _ => .local 1
  .ite inner (.call 1 [inner, .local 1, .local 2]) own

/-- `Root(first, real, dictionary)` with a dictionary in slot 3, a cell in
    slot 4 and a carrier in slot 5. `use` says where `first` goes and what is
    executed. With `fresh`, slots 6 and 7 stand for the first two parameters:
    two executable carriers of the root's own, which no caller has seen. -/
private def root (incoming fresh : Bool) (use : String) : Expr :=
  let first' := if fresh then 6 else 0
  let real := if fresh then 7 else 1
  let up (payload witness : Nat) : Expr := .seq
    (.assign 4 (.heap (.new 0) [.local payload]))
    (.assign 5 (.call 1 [.local 3, .prim .mkArr [.local 4], .local witness]))
  let execute (value : Expr) : Expr := .call 0 [.heap (.get 0) [value]]
  let body := match use with
    -- the cell holds it; the cell is read through the coercion's result
    | "read-result" => Expr.seq (up first' real) (execute (first (.local 5)))
    -- it is written through the coercion's result; the cell itself is read
    | "write-result" => .seq (up real real)
        (.seq (.heap (.set 0) [first (.local 5), .local first']) (execute (.local 4)))
    -- the coercion gets it as its witness, and the cell itself is read
    | "witness-cell" => .seq (up real first') (execute (.local 4))
    -- the coercion gets it as its witness, and its result is read
    | "witness-result" => .seq (up real first') (execute (first (.local 5)))
    -- the coercion gets it in the cell
    | _ => .seq (up first' real) (.lit .void)
  if incoming then .seq (.assign 3 (.local 2)) body else body

private def classify (family incoming : Bool) (shape use : String) (metadata : Bool) : IO Bool := do
  let sink : Fn := { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void }
  let up : Fn := {
    name := if family then "$subtypeCompose.Up" else "Control.Up"
    arity := 3, nslots := 3, decides := true, writes := true, body := coercion shape }
  let caller : Fn := {
    name := "Root", arity := 3, nslots := 8, decides := true, writes := true
    body := .seq (.assign 3 (.heap (.new 3) [.heap (.new 3) [.heap (.new 2) []]]))
      (.seq (.assign 4 (.heap (.new 0) [.heap (.new 1) []]))
        (.seq (.assign 5 (.lit (.arr #[])))
          (.seq (.assign 6 (.heap (.new 1) [])) (.seq (.assign 7 (.heap (.new 1) []))
            (root incoming (!metadata && !incoming) use))))) }
  let closed : Fn := { name := "ClosedRoot", arity := 0, nslots := 0, decides := false, body := .lit .void }
  let fns := #[sink, up, caller, closed]
  let sigs : Sigs := {
    fns := [([callable], .void), ([composed, carrier, callable], carrier),
      ([callable, callable, composed], .void), ([], .void)]
    classes := [[.var 0], [], [], [dictionary]], pins := [[none], [], [], []] }
  let slots := [[callable], [composed, carrier, callable],
    [callable, callable, composed, composed, cell, carrier, callable, callable], []]
  let prog : Prog := { fns := fns.toList, main := 3 }
  let valid := prog.check && prog.checkControl && prog.checkTypes sigs slots && checkPrelude prog sigs
  unless valid do
    throw <| IO.userError s!"INVALID inert-coercion model {shape}/{use}: check={prog.check} control={prog.checkControl} types={prog.checkTypes sigs slots} prelude={checkPrelude prog sigs}"
  let infos : Array MetadataFlow.Info := fns.mapIdx fun index fn => {
    body := some fn.body
    cellTag := some 0
    cellHelper := index == 0
    nonCellSlots := if index == 1 then [0] else if index == 2 then [2, 3] else []
    cellSlots := if index == 2 then [4] else []
    inputs := if index == 2 && metadata then [0] else []
    required := if index == 0 then [0] else [] }
  let results := sigs.fns.toArray.map fun (_, result) => MetadataValues.objectFree result
  let actual := MetadataFlow.check fns infos #[[], [], [], []] false results
  let admitted := match actual with | .ok _ => true | .error _ => false
  IO.println s!"family={family} incoming={incoming} shape={shape} use={use} metadata={metadata} admitted={admitted}"
  return admitted

private def models : IO Unit := do
  let mut bad := 0
  let mut count := 0
  -- (shape, use, whether metadata in the first parameter reaches Execute,
  --  whether the all-real program is admitted)
  for (shape, use, executes, real) in [
      ("identity", "read-result", true, true), ("identity", "write-result", true, true),
      ("identity", "witness-cell", false, true), ("identity", "witness-result", false, true),
      ("store", "witness-cell", true, true), ("store", "witness-result", true, true),
      ("build", "witness-result", true, true), ("build", "witness-cell", false, true),
      -- the coercion is its own entry, where the incoming cell is unknown
      ("read", "coerce", true, false)] do
    for incoming in [false, true] do
      for metadata in [false, true] do
        let control ← classify false incoming shape use metadata
        let certified ← classify true incoming shape use metadata
        count := count + 2
        -- Metadata that reaches Execute is refused, under the family's name
        -- exactly as under the control's.
        if metadata && executes && (control || certified) then bad := bad + 1
        -- The transfer may refuse more than the replay, never less.
        if certified && !control then bad := bad + 1
        -- With arguments of the root's own, an all-real program is admitted:
        -- the unknown alias reads the join of the known cells. An incoming
        -- dictionary is an unseen caller value, and so is what it coerces.
        if !metadata && !incoming && real && !(control && certified) then bad := bad + 1
        if !metadata && !real && (control || certified) then bad := bad + 1
  IO.println s!"{count} inert-coercion policy classifications; {bad} mismatches"
  if bad > 0 then throw <| IO.userError "inert coercion policy mismatch"

/-- One coercion: the bound and its constraint, further parameters and
    their arguments, the use of the coerced `Stored`, the caller's type and
    value, and whether that use executes the value. -/
private structure Family where
  name : String
  bound : String
  constraint : String
  parameters : String := ""
  arguments : String := ""
  use : String
  callerType : String
  value : String
  executes : Bool := true

private def families : List Family := [
  { name := "identity", bound := "base", constraint := "t:subtype(base)"
    use := "Stored.Get()", callerType := "base", value := "base{}" },
  { name := "nominal", bound := "base", constraint := "t:subtype(base)"
    use := "Stored.Get()", callerType := "derived", value := "derived{}" },
  { name := "compose", bound := "base", constraint := "u:subtype(base),t:subtype(u)"
    parameters := ",U:u", arguments := ",base{}"
    use := "Stored.Get()", callerType := "derived", value := "derived{}" },
  { name := "array", bound := "[]base", constraint := "t:subtype([]base)"
    use := "if(S:=Stored[0]) then S.Get() else 0", callerType := "[]derived", value := "array{derived{}}" },
  { name := "option", bound := "?base", constraint := "t:subtype(?base)"
    use := "if(S:=Stored?) then S.Get() else 0", callerType := "?derived", value := "option{derived{}}" },
  { name := "map", bound := "[int]base", constraint := "t:subtype([int]base)"
    use := "if(S:=Stored[1]) then S.Get() else 0", callerType := "[int]derived", value := "map{1=>derived{}}" },
  -- No use of an `any`, a `void` or a `rational` executes it.
  { name := "erase", bound := "any", constraint := "t:subtype(any)"
    use := "7", callerType := "base", value := "base{}", executes := false },
  { name := "discard", bound := "void", constraint := "t:subtype(void)"
    use := "7", callerType := "base", value := "base{}", executes := false },
  { name := "rational", bound := "rational", constraint := "t:subtype(rational)"
    use := "if(Stored=7) then 7 else 0", callerType := "int", value := "7", executes := false }]

/-- `direct` uses the coerced value, `cell` the captured `var` it was stored
    in, and `kept` stores it without a use. -/
private def source (f : Family) (shape : String) : String :=
  let cell := shape != "direct"
  let use := if shape == "kept" then "7" else if cell then f.use.replace "Stored" "Kept" else f.use
  "base:=class<computes>{\n    N:int=7\n    Get()<computes>:int=N}\n" ++
  "derived:=class<computes>(base){}\n" ++
  "Produce(F:t,Dummy:t" ++ f.parameters ++ " where " ++ f.constraint ++ ")<transacts>:int=\n" ++
  "    var Steps:int=0\n" ++
  (if cell then "    var Kept:" ++ f.bound ++ "=F\n" else "") ++
  "    for(V:=(3|7)):\n" ++
  "        set Steps+=1\n" ++
  "        Stored:" ++ f.bound ++ "=Dummy\n" ++
  (if cell then "        set Kept=Stored\n" else "") ++
  "        if(V=7):return (" ++ use ++ ")|(" ++ use ++ ")+1000\n" ++
  "    0\n" ++
  "Caller(F:" ++ f.callerType ++ ",Dummy:" ++ f.callerType ++ ")<transacts>:int=\n" ++
  "    Rows:=for(G:=Produce(F,Dummy" ++ f.arguments ++ ")):\n" ++
  "        Print(\"got {G}\")\n" ++
  "        1\n" ++
  "    Rows.Length\n" ++
  "Main()<transacts>:void=Print(\"count {Caller(" ++ f.value ++ "," ++ f.value ++ ")}\")\n"

private def compile (text : String) (dummy : Bool) : Except String Compiled := do
  let tops ← parseProgram text
  let tops := tops.map fun
    | .fn p name params tparams specs ret body =>
      .fn p name (params.map fun param =>
        { param with typeValue := dummy && name == "Caller" && param.name == "Dummy" })
        tparams specs ret body
    | other => other
  elabProgram tops {}

private def pairs (out : String) : IO Unit := do
  let expected := "got 7\ngot 1007\ncount 2\n"
  let mut count := 0
  let mut oracles := 0
  for f in families do
    for shape in (if f.executes then ["direct", "cell", "kept"] else ["direct", "cell"]) do
      for dummy in [false, true] do
        let tag := s!"{f.name}-{shape}-{dummy}"
        let admitted := !dummy || !f.executes || shape == "kept"
        let start ← IO.monoMsNow
        match compile (source f shape) dummy with
        | .error message =>
          unless !admitted && (message.splitOn "dummy type value cannot").length > 1 do
            throw (IO.userError s!"unexpected inert-coercion refusal: {tag}: {message}")
        | .ok compiled =>
          unless admitted && compiled.prog.check && compiled.prog.checkControl &&
              compiled.prog.checkTypes compiled.sigs compiled.slotTys do
            throw (IO.userError s!"unexpected inert-coercion admission or Core mismatch: {tag}")
          match compiled.prog.runB 10000000 10000 with
          | .res (.ok _, output) =>
            unless String.ofList (output.map Char.ofNat) == expected do
              throw (IO.userError s!"inert-coercion output mismatch: {tag}")
          | _ => throw (IO.userError s!"inert-coercion VM failure: {tag}")
          IO.FS.writeBinFile s!"{out}/{tag}.vbc" compiled.prog.encode
          IO.FS.writeFile s!"{out}/{tag}.expected" expected
          oracles := oracles + 1
        count := count + 1
        IO.println s!"{tag} admitted={admitted} elapsed_ms={(← IO.monoMsNow) - start}"
        (← IO.getStdout).flush
  IO.println s!"inert-coercion source: {count} API classifications, {oracles} complete Lean oracles"

def main (args : List String) : IO Unit := do
  let out := args.headD "/tmp/openverse-inert-coercions"
  IO.FS.createDirAll out
  models
  pairs out
end MetadataInertCoercions

def main (args : List String) : IO Unit := MetadataInertCoercions.main args
