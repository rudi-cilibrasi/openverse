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

private def witness (p : Pos) (base derived : STy) : SExpr :=
  .app p (.ident p "$subtypeWitness") [.construct p family [base, derived] []] false

private def rewrite (body : SExpr) : Except String SExpr := do
  let rename (n : String) := if n == "evidence" then family else n
  let resolver : Resolver := {
    val := fun _ n => pure (rename n), ty := fun _ n => pure (rename n),
    bind := fun _ _ => pure (), qual := fun _ _ => pure none }
  let body := Choice.mapE (fun
    | .app p (.ident _ "IntProof") [] false => some (witness p (.name "int") (.name "small"))
    | .app p (.ident _ "RatProof") [] false => some (witness p (.name "rational") (.name "small"))
    | .app p (.ident _ "WideProof") [] false => some (witness p (.name "wide") (.name "small"))
    | .app p (.ident _ "FloatProof") [] false => some (witness p (.name "float") (.name "fsmall"))
    | .app p (.ident _ "NumericProof") [] false => some (witness p (.name "rational") (.name "int"))
    | _ => none) body
  body.mapNamesM resolver

private partial def rewriteTop : STop → Except String STop
  | .fn p name ps tps specs ret body => do
    let rename (n : String) : Except String String := pure (if n == "evidence" then family else n)
    let ps ← ps.mapM fun param => do
      return { param with ty := ← param.ty.mapNamesM rename, default := ← param.default.mapM rewrite }
    return .fn p name ps tps specs (← ret.mapNamesM rename) (← rewrite body)
  | .classDef p name tps specs parents iface fields overrides methods => do
    let rename (n : String) : Except String String := pure (if n == "evidence" then family else n)
    let fields ← fields.mapM fun (name, ty, value, mutable) => do
      return (name, ← ty.mapNamesM rename, ← value.mapM rewrite, mutable)
    return .classDef p name tps specs (← parents.mapM (·.mapNamesM rename)) iface fields overrides
      (← methods.mapM rewriteTop)
  | .const p name ty body => return .const p name ty (← rewrite body)

private def compile (name source : String) (profile : SourceProfile := .full) : IO Compiled := do
  let parsed ← getOK (name ++ ": parse") (parseProgram source)
  let tops ← getOK (name ++ ": rewrite") (parsed.mapM rewriteTop)
  getOK (name ++ ": compile") (elabProgram tops { profile })

private def domains := "
small:=type{_X:int where 0 <= _X, _X <= 10}
wide:=type{_X:int where -10 <= _X, _X <= 20}
fsmall:=type{_X:float where 0.0 <= _X, _X <= 10.0}
"

private def generics := "
UseScalar(X:u,D:evidence(t,u) where t:type,u:type)<computes>:t=X
UseTuple(X:tuple(u,u),D:evidence(t,u) where t:type,u:type)<computes>:[]t=X
"

private def producers := "
counter:=class<allocates>{var N:int=0}
Small(C:counter)<transacts>:small=
    set C.N+=1
    Print(\"small {C.N}\")
    7
Item(C:counter,V:int)<transacts>:int=
    set C.N+=1
    Print(\"item {C.N} {V}\")
    V
Pair(C:counter)<transacts>:tuple(int,int)=(Item(C,7),Item(C,8))
"

private def stateMain := "
Main():void=
    C:=counter{}
    S:=Small(C)
    N:=UseScalar(S,IntProof())
    Print(\"refinement {N}\")
    R:=UseScalar(S,RatProof())
    if(R=7):Print(\"refined rational 7\")
    W:=UseScalar(S,WideProof())
    Print(\"interval {W}\")
    F:fsmall=2.5
    G:=UseScalar(F,FloatProof())
    if(G=2.5):Print(\"refined float 2.5\")
    D:=NumericProof()
    A:=UseTuple(Pair(C),D)
    if(X:=A[0],Y:=A[1],X=7,Y=8):Print(\"tuple array 7 8 {A.Length}\")
    if(UseTuple(Pair(C),D),false?)then Print(\"bad\")else Print(\"rolled tuple\")
    Print(\"count {C.N}\")
"

private def stateSource := domains ++ generics ++ producers ++ stateMain

private def stateControl := domains ++ producers ++ "
AsInt(X:small)<computes>:int=X
AsRat(X:small)<computes>:rational=X
AsWide(X:small)<computes>:wide=X
AsFloat(X:fsmall)<computes>:float=X
AsArray(X:tuple(int,int))<computes>:[]rational=X
" ++ (stateMain
  |>.replace "UseScalar(S,IntProof())" "AsInt(S)"
  |>.replace "UseScalar(S,RatProof())" "AsRat(S)"
  |>.replace "UseScalar(S,WideProof())" "AsWide(S)"
  |>.replace "UseScalar(F,FloatProof())" "AsFloat(F)"
  |>.replace "    D:=NumericProof()\n" ""
  |>.replace "UseTuple(Pair(C),D)" "AsArray(Pair(C))")

private def stateTrace := "small 1\nrefinement 7\nrefined rational 7\ninterval 7\nrefined float 2.5\nitem 2 7\nitem 3 8\ntuple array 7 8 2\nrolled tuple\ncount 3\n"

private def cancelSource := domains ++ generics ++ "
holder(t:type):=class<computes>:
    X:t
    D:evidence(int,t)
    Read()<computes>:int=UseScalar(X,D)
Worker(X:t,D:evidence(int,t) where t:type)<suspends>:void=
    H:=holder(t){X:=X,D:=D}
    F:type{_()<computes>:int}=H.Read
    defer:Print(\"cleanup {F()}\")
    Sleep(10.0)
    Print(\"bad\")
Main()<suspends>:void=
    S:small=7
    race:
        Worker(S,IntProof())
        block:
            Sleep(0.0)
            Print(\"winner\")
    Print(\"after\")
"

private def cancelControl := domains ++ "
holder:=class<computes>:
    X:small
    Read()<computes>:int=X
Worker(X:small)<suspends>:void=
    H:=holder{X:=X}
    F:type{_()<computes>:int}=H.Read
    defer:Print(\"cleanup {F()}\")
    Sleep(10.0)
    Print(\"bad\")
Main()<suspends>:void=
    S:small=7
    race:
        Worker(S)
        block:
            Sleep(0.0)
            Print(\"winner\")
    Print(\"after\")
"

private def contracts : IO Unit := do
  let types : TyEnv := { refines := [
    ("small", .int, [(">=", .int 0), ("<=", .int 10)]),
    ("wide", .int, [(">=", .int (-10)), ("<=", .int 20)]),
    ("strict", .int, [(">", .int (-1)), ("<", .int 11)])] }
  for base in [Ty.int, .rational, .refine "wide", .refine "strict"] do
    let some plan := find? types [] ⟨base, .refine "small"⟩
      | throw (IO.userError "missing refinement widening")
    need "refinement evidence matches declaration entailment"
      (plan.valid types [] && types.boundSubtype (.refine "small") base)
    need "refinement requests retain the actual source and result"
      (plan.refinements == [("small", base)] && plan.bound types == ⟨base, .refine "small"⟩)
  need "literal membership does not establish int subtyping a refinement"
    ((find? types [] ⟨.refine "small", .int⟩).isNone && !types.boundSubtype .int (.refine "small"))
  need "interval narrowing and cross-base conversions stay refused"
    ((find? types [] ⟨.refine "small", .refine "wide"⟩).isNone &&
      (find? types [] ⟨.float, .refine "small"⟩).isNone)
  need "missing refinement metadata cannot make evidence"
    (!(Plan.refinement "missing" .int).valid types [])
  let tps := [TParam.withUpperBound { line := 1, col := 1 } "a" (.name "small"),
    TParam.withUpperBound { line := 1, col := 1 } "b" (.name "a")]
  let resolved ← getOK "numeric refinement formal bounds" (resolveTParams types tps)
  need "numeric refinement comparability follows peer chains"
    (resolved.params == [("a", true), ("b", true)])
  let t := Ty.param "t" false
  let u := Ty.param "u" false
  let locals := [("Element", (Bound.mk t u).ty)]
  let some tuplePlan := find? {} locals ⟨.arr t, .tup [u, u]⟩
    | throw (IO.userError "missing tuple-array component evidence")
  need "tuple-array plans retain each component's real evidence"
    (tuplePlan.valid {} locals && tuplePlan.usesLocal && tuplePlan.tupleArrayArities == [2])
  need "missing components do not make a tuple-array proof"
    ((find? {} [] ⟨.arr t, .tup [u, u]⟩).isNone &&
      !(Plan.tupleArray t [.identity .int]).valid {} [])
  need "void is not silently treated as an empty array"
    (!(Plan.tupleArray t []).valid {} [] && (tupleArrayDeclaration { line := 1, col := 1 } 0).toOption.isNone &&
      (find? {} [] ⟨.arr t, .void⟩).isNone)
  let peer := [Bound.mk t u, Bound.mk t (.param "v" false)]
  for actual in [[("u", Ty.tup [.int, .int]), ("v", Ty.arr .rational)],
      [("v", Ty.arr .rational), ("u", Ty.tup [.int, .int])]] do
    let some inferred := SubtypeEvidence.infer {} peer actual true
      | throw (IO.userError "mixed tuple-array inference")
    need "mixed peer inference preserves the common array upper" (inferred.lookup "t" == some (.arr .rational))
  let deep := fun (base : Ty) => (List.range 20).foldl (fun ty _ => Ty.arr ty) base
  let some inferred := SubtypeEvidence.infer {} peer [("u", deep .int), ("v", deep .rational)] true
    | throw (IO.userError "nested component inference")
  need "nested matching containers keep their shape" (inferred.lookup "t" == some (deep .rational))

def main (args : List String) : IO Unit := do
  contracts
  for (name, source, expected) in [("relation-state", stateSource, stateTrace),
      ("relation-state-control", stateControl, stateTrace),
      ("relation-cancel", cancelSource, "winner\ncleanup 7\nafter\n"),
      ("relation-cancel-control", cancelControl, "winner\ncleanup 7\nafter\n")] do
    let compiled ← compile name source
    let strict ← compile (name ++ " choice-free") source .choiceFree
    need (name ++ ": profile preservation") (compiled.prog.encode == strict.prog.encode)
    need (name ++ ": checked Core") (compiled.prog.check && compiled.prog.checkControl &&
      compiled.prog.checkTypes compiled.sigs compiled.slotTys)
    match compiled.prog.runB 1000000 10000 with
    | .res (.ok _, output) => need (name ++ ": exact trace") (String.ofList (output.map Char.ofNat) == expected)
    | _ => throw (IO.userError (name ++ ": execution failed"))
    if let [out] := args then
      IO.FS.writeBinFile s!"{out}/{name}.vbc" compiled.prog.encode
      IO.FS.writeFile s!"{out}/{name}.expected" expected
  IO.println "ordinary subtype relation contracts passed (refinements, tuple-array, inference, state, rollback, escaping cleanup)"
