# (#761) Overloaded functions and methods, one overload with several
# values, in a `for` with a composed choice. The clauses after the choice
# are in the for's search once, so a call among them picks its overload as
# anywhere, and a row that reaches no body is undone. `Inner` adds 100 and
# gives an element only for V = 1. The controls have the same rows from a
# written choice of values.
Cell := class{var N:int = 0}
C(S:Cell)<transacts><decides>:void =
    S.N >= 0
Inner(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (V = 1) then array{1} else array{}
Ow(A:int)<computes>:int = A * 5
Ow(T:string)<computes>:int = T.Length | 9
Ow(A:int, B:int)<computes>:int = Ow(A) | Ow("{B}")
base := class:
    Mv(P:int)<transacts>:int = P + 2 | P
    Mv(P:int, Q:int)<transacts>:int = P * 10 + Q
derived := class(base):
    Mv<override>(P:int)<transacts>:int = P * 3 | (super:)Mv(P) | P - 1
# The overloads after the choice: X is 5 times V, Y is 2 then 9. The rows
# with V = 3 and V = 5 are undone; V = 1 has two rows.
After(S:Cell)<transacts>:void =
    for (V := (if (C[S]) then (3 | 5) else 4) | 1, X := Ow(V), Y := Ow("ab"), W : Inner(S, V)):
        Print("after {V} {X} {Y} {W} {S.N}")
AfterControl(S:Cell)<transacts>:void =
    for (V := (3 | 5 | 1), X := (V * 5), Y := (2 | 9), W : Inner(S, V)):
        Print("after {V} {X} {Y} {W} {S.N}")
# The two-argument overload is the choice: 15, then 1 and 9. Only 9 gives
# `Inner` a 1.
Pair(S:Cell)<transacts>:void =
    for (V := Ow(3, 7), W : Inner(S, V - 8)):
        Print("pair {V} {W} {S.N}")
PairControl(S:Cell)<transacts>:void =
    for (V := (15 | 1 | 9), W : Inner(S, V - 8)):
        Print("pair {V} {W} {S.N}")
# An overloaded method, overridden: 3, the parent's 3 and 1, then 0.
Method(S:Cell)<transacts>:void =
    B:base = derived{}
    for (V := B.Mv(1), W : Inner(S, V)):
        Print("method {V} {B.Mv(V, 2)} {W} {S.N}")
MethodControl(S:Cell)<transacts>:void =
    for (V := (3 | 3 | 1 | 0), W : Inner(S, V)):
        Print("method {V} {V * 10 + 2} {W} {S.N}")
Run(Name:string, F(:Cell)<transacts>:void)<transacts>:void =
    S := Cell{}
    F(S)
    Print("{Name} state {S.N}")
Main()<transacts>:void =
    Run("after", After)
    Run("after", AfterControl)
    Run("pair", Pair)
    Run("pair", PairControl)
    Run("method", Method)
    Run("method", MethodControl)
