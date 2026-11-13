import OpenVerse.Front.Elab
import OpenVerse.Core.Bounded
import OpenVerse.Core.Encode

open OpenVerse OpenVerse.Front OpenVerse.Front.SubtypeEvidence

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def getOK (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{label}: {message}")

private def p : Pos := { line := 1, col := 1 }

private def rewrite (body : SExpr) : Except String SExpr := do
  let rename (name : String) := if name == "evidence" then family else name
  let resolver : Resolver := {
    val := fun _ name => pure (rename name), ty := fun _ name => pure (rename name),
    bind := fun _ _ => pure (), qual := fun _ _ => pure none }
  let body := Choice.mapE (fun
    | .app q (.ident _ "Numeric") [] false => some (.app q (.ident q "$subtypeWitness")
        [.construct q family [.name "rational", .name "int"] []] false)
    | _ => none) body
  body.mapNamesM resolver

private partial def rewriteTop : STop → Except String STop
  | .fn q name ps tps specs ret body => do
    let rename (n : String) : Except String String := pure (if n == "evidence" then family else n)
    let ps ← ps.mapM fun param => do
      return { param with ty := ← param.ty.mapNamesM rename, default := ← param.default.mapM rewrite }
    return .fn q name ps tps specs (← ret.mapNamesM rename) (← rewrite body)
  | .classDef q name nsp tps specs parents iface fields methods => do
    let rename (n : String) : Except String String := pure (if n == "evidence" then family else n)
    let fields ← fields.mapM fun f => do
      return { f with ty := ← f.ty.mapNamesM rename, default := ← f.default.mapM rewrite }
    return .classDef q name nsp tps specs (← parents.mapM (·.mapNamesM rename)) iface fields
      (← methods.mapM rewriteTop)
  | .const q name sp ty body => return .const q name sp ty (← rewrite body)

private def compile (label source : String) (profile : SourceProfile := .full) : IO Compiled := do
  let parsed ← getOK (label ++ ": parse") (parseProgram source)
  let tops ← getOK (label ++ ": rewrite") (parsed.mapM rewriteTop)
  getOK (label ++ ": elaborate") (elabProgram tops { profile })

private def header := "
ArrayUp(X:[]u,D:evidence(t,u) where t:type,u:type)<computes>:[]t=X
OptionUp(X:?u,D:evidence(t,u) where t:type,u:type)<computes>:?t=X
MapUp(X:[int]u,D:evidence(t,u) where t:type,u:type)<computes>:[int]t=X
KeyMapUp(X:[k]u,Keys:evidence(j,k),D:evidence(t,u) where j:subtype(comparable),k:subtype(comparable),t:type,u:type)<computes>:[j]t=X
TupleUp(X:tuple(u,string),D:evidence(t,u) where t:type,u:type)<computes>:tuple(t,string)=X
TripleUp(X:tuple(u,string,u),D:evidence(t,u) where t:type,u:type)<computes>:tuple(t,string,t)=X
Nested(X:[]?tuple(u,string),D:evidence(t,u) where t:type,u:type)<computes>:[]?tuple(t,string)=X
holder(t:type,u:type):=class<computes>:
    Values:[]u
    D:evidence(t,u)
    Read()<computes>:[]t=ArrayUp(Values,D)
"

private def stateSource := header ++ "
counter:=class<allocates>{var N:int=0}
Value(C:counter)<transacts>:[]int=
    set C.N+=1
    Print(\"value {C.N}\")
    array{7,3}
Main():void=
    C:=counter{}
    D:=Numeric()
    A:=ArrayUp(Value(C),D)
    if(V:=A[0],V=7):Print(\"array 7 {A.Length}\")
    if(ArrayUp(Value(C),D),false?)then Print(\"bad\")else Print(\"rolled\")
    Print(\"count {C.N}\")
    E:[]int=array{}
    Print(\"empty {ArrayUp(E,D).Length}\")
    O:?int=false
    if(OptionUp(O,D)?)then Print(\"bad\")else Print(\"none\")
    if(V:=OptionUp(option{8},D)?,V=8):Print(\"some 8\")
    M:=MapUp(map{2=>9,1=>4},D)
    if(V:=M[2],V=9):Print(\"map 9 {M.Length}\")
    K:=KeyMapUp(map{2=>14,1=>15},D,D)
    if(V:=K[2],V=14):Print(\"keys 14 {K.Length}\")
    ME:[int]int=map{}
    Print(\"empty map {MapUp(ME,D).Length}\")
    T:=TupleUp((10,\"tag\"),D)
    if(T(0)=10):Print(\"tuple 10 {T(1)}\")
    Triple:=TripleUp((16,\"tail\",17),D)
    if(Triple(0)=16,Triple(2)=17):Print(\"triple 16 {Triple(1)} 17\")
    Input:[]?tuple(int,string)=array{false,option{(11,\"nested\")}}
    N:=Nested(Input,D)
    if(O2:=N[0],O2?)then Print(\"bad\")else Print(\"nested none\")
    if(O2:=N[1],T2:=O2?,T2(0)=11):Print(\"nested 11 {T2(1)}\")
    H:=holder(rational,int){Values:=array{12},D:=D}
    F:type{_()<computes>:[]rational}=H.Read
    B:=F()
    if(V:=B[0],V=12):Print(\"escaped 12\")
"

private def stateTrace := "value 1\narray 7 2\nrolled\ncount 1\nempty 0\nnone\nsome 8\nmap 9 2\nkeys 14 2\nempty map 0\ntuple 10 tag\ntriple 16 tail 17\nnested none\nnested 11 nested\nescaped 12\n"

private def cancelSource := header ++ "
Worker(X:[]u,D:evidence(rational,u) where u:type)<suspends>:void=
    A:[]rational=X
    H:=holder(rational,u){Values:=X,D:=D}
    F:type{_()<computes>:[]rational}=H.Read
    defer:
        B:=F()
        if(V:=A[0],W:=B[0],V=7,W=7):Print(\"cleanup 7\")
    Sleep(10.0)
    Print(\"bad\")
Main()<suspends>:void=
    D:=Numeric()
    race:
        Worker(array{7},D)
        block:
            Sleep(0.0)
            Print(\"winner\")
    Print(\"after\")
"

private def cancelTrace := "winner\ncleanup 7\nafter\n"

/-- The independent control uses ordinary concrete container coercions,
    which predate the evidence path. It shares neither the new plans nor
    the new component-dictionary traversal. -/
private def concrete (source : String) : String := source
  |>.replace "where j:subtype(comparable),k:subtype(comparable),t:type,u:type" ""
  |>.replace "where t:type,u:type" ""
  |>.replace "where u:type" ""
  |>.replace "holder(t:type,u:type)" "holder"
  |>.replace "holder(rational,int)" "holder"
  |>.replace "holder(rational,u)" "holder"
  |>.replace "evidence(t,u)" "evidence(rational,int)"
  |>.replace "evidence(rational,u)" "evidence(rational,int)"
  |>.replace "evidence(j,k)" "evidence(rational,int)"
  |>.replace "[k]u" "[int]int"
  |>.replace "[j]t" "[rational]rational"
  |>.replace "tuple(u,string,u)" "tuple(int,string,int)"
  |>.replace "tuple(t,string,t)" "tuple(rational,string,rational)"
  |>.replace "tuple(u,string)" "tuple(int,string)"
  |>.replace "tuple(t,string)" "tuple(rational,string)"
  |>.replace "[]u" "[]int"
  |>.replace "[]t" "[]rational"
  |>.replace "X:?u," "X:?int,"
  |>.replace ">:?t=" ">:?rational="
  |>.replace "[int]u" "[int]int"
  |>.replace "[int]t" "[int]rational"

private def mapSource := header ++ "
Raw()<computes>:[int]int=map{}
Main():void=
    M:=MapUp(Raw(),Numeric())
    Print(\"entries {M.Length}\")
    for(K->V:M):
        if(K=2,V=7)then Print(\"2:7\")else if(K=2,V=8)then Print(\"2:8\")else if(K=1,V=9)then Print(\"1:9\")else Print(\"bad entry\")
"

private def contracts : IO Unit := do
  let t := Ty.param "t" false
  let u := Ty.param "u" false
  let v := Ty.param "v" false
  let locals := [("Element", (Bound.mk t u).ty)]
  let facts := { ({} : TyEnv) with boundFacts := [(t, u)] }
  for (base, derived) in [(Ty.arr t, Ty.arr u), (.opt t, .opt u),
      (.map .int t, .map .int u), (.tup [t, .arr t], .tup [u, .arr u]),
      (.arr (.opt (.tup [t, .arr t])), .arr (.opt (.tup [u, .arr u])))] do
    let some plan := find? {} locals ⟨base, derived⟩
      | throw (IO.userError "missing structural plan")
    need "structural plan carries actual lexical evidence"
      (plan.valid {} locals && plan.usesLocal && plan.bound {} == ⟨base, derived⟩)
    need "declaration relation supports the same structural components" (facts.boundSubtype derived base)
    need "missing component proof remains refused" ((find? {} [] ⟨base, derived⟩).isNone)
    need "removing a captured proof invalidates the complete nested plan" (!plan.valid {} [])
  let whole := [("Whole", (Bound.mk (.arr t) (.arr u)).ty)]
  need "whole-container proof does not prove an element relation"
    ((find? {} whole ⟨t, u⟩).isNone &&
      !({ ({} : TyEnv) with boundFacts := [(.arr t, .arr u)] }.boundSubtype u t))
  need "a whole-container proof remains directly usable" ((find? {} whole ⟨.arr t, .arr u⟩).isSome)
  need "map keys widen through checked comparable evidence"
    ((find? {} [] ⟨.map .rational .rational, .map .int .int⟩).any fun plan => plan.valid {} [])
  let j := Ty.param "j" true
  let k := Ty.param "k" true
  need "a value proof cannot substitute for missing key evidence"
    ((find? {} locals ⟨.map j t, .map k u⟩).isNone)
  let keyLocals := ("Key", (Bound.mk j k).ty) :: locals
  need "keys and values use their own real lexical proofs"
    ((find? {} keyLocals ⟨.map j t, .map k u⟩).any fun plan => plan.valid {} keyLocals)
  need "map key narrowing is refused" ((find? {} [] ⟨.map .int .rational, .map .rational .int⟩).isNone)
  need "tuple arity stays exact" ((find? {} [] ⟨.tup [.rational], .tup [.int, .int]⟩).isNone)
  need "an API plan cannot invent comparable map keys" (!(Plan.map (.identity t) (.identity .int)).valid {} [])
  let composed := locals ++ [("After", (Bound.mk v (.arr t)).ty)]
  need "component conversion can precede a whole-container capability"
    ((find? {} composed ⟨v, .arr u⟩).any fun plan => plan.valid {} composed)
  let cycles := [("Grow", (Bound.mk (.arr t) t).ty), ("Shrink", (Bound.mk t (.arr t)).ty)]
  need "recursive container constraints terminate without fabricating a proof"
    ((find? {} cycles ⟨v, t⟩).isNone)
  let relation := [Bound.mk t u, Bound.mk t v]
  let some inferred := SubtypeEvidence.infer {} relation [("u", .arr .int), ("v", .arr .rational)] true
    | throw (IO.userError "container peer inference found no common upper")
  need "container peer inference chooses the component upper" (inferred.lookup "t" == some (.arr .rational))
  need "tuple materialization deduplicates its arity"
    ((Plan.tuple [.tuple [.rational, .rational], .rational]).tupleArities == [2])
  need "map keys retain component materialization requests"
    ((Plan.map (.tuple [.rational, .identity .string]) (.identity .int)).tupleArities == [2] &&
      (Plan.map (.nominal "child" "base" []) (.identity .int)).nominals == [("child", "base")])

def main (args : List String) : IO Unit := do
  contracts
  let mut artifacts := []
  for (name, source, expected) in [("container-state", stateSource, stateTrace),
      ("container-state-control", concrete stateSource, stateTrace),
      ("container-cancel", cancelSource, cancelTrace),
      ("container-cancel-control", concrete cancelSource, cancelTrace)] do
    let compiled ← compile name source
    let strict ← compile (name ++ " choice-free") source .choiceFree
    need (name ++ ": admitted source preserves profile bytecode") (compiled.prog.encode == strict.prog.encode)
    artifacts := artifacts ++ [(name, compiled, expected)]
  let keyMapSource := mapSource.replace "MapUp(Raw(),Numeric())" "KeyMapUp(Raw(),Numeric(),Numeric())"
  for (name, source) in [("container-map-order", mapSource), ("container-map-order-control", concrete mapSource),
      ("container-map-key-order", keyMapSource), ("container-map-key-order-control", concrete keyMapSource)] do
    let compiled ← compile name source
    -- Exercise all values admitted by the map's Core type, including raw
    -- duplicate keys. A conversion must not silently canonicalize entries.
    let raw := Expr.prim .mkArr ([7, 8, 9].zip [2, 2, 1] |>.map fun (value, key) =>
      Expr.prim .mkTup [.lit (.int key), .lit (.int value)])
    need "raw map producer is present" (compiled.prog.fns.any (·.name == "Raw"))
    let compiled := { compiled with prog := { compiled.prog with fns := compiled.prog.fns.map fun fn =>
      if fn.name == "Raw" then { fn with body := raw } else fn } }
    artifacts := artifacts ++ [(name, compiled, "entries 3\n2:7\n2:8\n1:9\n")]
  for (name, compiled, expected) in artifacts do
    need (name ++ ": checked Core") (compiled.prog.check && compiled.prog.checkControl &&
      compiled.prog.checkTypes compiled.sigs compiled.slotTys)
    match compiled.prog.runB 1000000 10000 with
    | .res (.ok _, output) =>
      need (name ++ ": independent trace") (String.ofList (output.map Char.ofNat) == expected)
    | _ => throw (IO.userError (name ++ ": execution failed"))
    if let [out] := args then
      IO.FS.writeBinFile s!"{out}/{name}.vbc" compiled.prog.encode
      IO.FS.writeFile s!"{out}/{name}.expected" expected
  IO.println "subtype container contracts passed (components, empties, order, rollback, escape, cancellation, exact Lean/C artifacts)"
