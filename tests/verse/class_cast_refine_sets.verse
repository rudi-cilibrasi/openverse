# Refining casts whose branch sets vars from outside it (#243), each a copy in the branch, set after the
# if: one var and two, with and without an else that sets one too, op= forms, more clauses after the cast
# (with and without an else), a var at a type parameter, array elements (also in a loop), a method's var
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
    Bump(P:pair(a, b) where a:type, b:type)<transacts>:int =
        var Q:int = C
        if (D := dup[P]) then set Q += D.C
        Q
More(P:pair(a, b) where a:type, b:type):int =
    var N:int = 0
    if (D := dup[P], D.C > 2):
        set N = D.C
    N
MoreElse(P:pair(a, b) where a:type, b:type):int =
    var N:int = 0
    V := if (D := dup[P], D.C > 2):
        set N = D.C
        N * 2
    else:
        set N = -1
        0
    N + V
Gen(P:pair(a, b), X:a where a:type, b:type):a =
    var V:a = X
    if (D := dup[P]) then set V = D.B
    V
Arr(P:pair(a, b) where a:type, b:type):int =
    var Xs:[]int = array{1, 2, 3}
    if (D := dup[P]):
        if (set Xs[1] = D.C) {}
        for (I := 0..1) { if (set Xs[I] = Xs[I] + 10) {} }
    Xs[0] + Xs[1] + Xs[2] or 0
F(P:pair(a, b) where a:type, b:type):int =
    var N:int = 0
    if (D := dup[P]):
        set N = D.C
    N
G(P:pair(a, b), X:a where a:type, b:type):a =
    var N:int = 1
    var M:int = 2
    R := if (D := dup[P]):
        set N = N + D.C
        set M = N * 10
        D.B
    else:
        set M = 99
        X
    Print("N={N} M={M}")
    R
H(P:pair(a, b) where a:type, b:type):int =
    var K:int = 5
    if (D := dup[P]) then set K += D.C else set K = 0
    K
Main()<transacts>:void =
    Print("{F(dup(int){A := 1, B := 2, C := 7})} {F(pair(int, string){A := 1, B := "x"})}")
    Print("{G(dup(int){A := 1, B := 2, C := 3}, 9)}")
    Print("{G(pair(int, string){A := 1, B := "x"}, 9)}")
    Print("{H(dup(int){A := 1, B := 2, C := 4})} {H(pair(int, string){A := 1, B := "x"})}")
    Print("{More(dup(int){A := 1, B := 2, C := 5})} {More(dup(int){A := 1, B := 2, C := 1})} {More(pair(int, int){A := 1, B := 2})}")
    Print("{MoreElse(dup(int){A := 1, B := 2, C := 5})} {MoreElse(dup(int){A := 1, B := 2, C := 1})}")
    Print("{Gen(dup(int){A := 1, B := 7}, 3)} {Gen(pair(int, string){A := 1, B := "x"}, 3)}")
    Print("{Arr(dup(int){A := 1, B := 2, C := 9})} {Arr(pair(int, string){A := 1, B := "x"})}")
    Print("{dup(int){A := 1, B := 2, C := 4}.Bump(dup(int){A := 1, B := 2, C := 3})}")
