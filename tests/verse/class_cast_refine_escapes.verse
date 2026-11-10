# Refining casts whose branch has a return or a break that leaves it (#243): its function returns a tuple
# that says so, and the caller returns or breaks: a return as the whole branch, under an if that may
# fall through, in a void function, where the if's value is used (at its written type), with a set of a
# var from outside it, in a loop in the branch, with the enclosing function's defer:, with more clauses
# after the cast, and in a method
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
    Try(P:pair(a, b) where a:type, b:type):int =
        if (D := dup[P]):
            if (D.C = C) then return 1
        0
SR(P:pair(a, b) where a:type, b:type):int =
    var N:int = 10
    if (D := dup[P]):
        set N += D.C
        if (N > 12) then return N * 100
    N
Loop(P:pair(a, b) where a:type, b:type):int =
    if (D := dup[P]):
        for (I := 1..5):
            if (I = D.C) then return I * 1000
    -1
Def(P:pair(a, b) where a:type, b:type)<transacts>:int =
    defer: Print("fdefer")
    if (D := dup[P]):
        return D.C
    0
More(P:pair(a, b) where a:type, b:type):int =
    if (D := dup[P], D.C > 2):
        return D.C
    0
F(P:pair(a, b), X:a where a:type, b:type):b =
    if (D := dup[P]):
        return D.A
    else:
        P.B
G(P:pair(a, b) where a:type, b:type):int =
    if (D := dup[P]):
        if (D.C > 5) then return 100
        Print("small")
    Print("after")
    1
H(Ps:[]pair(a, b) where a:type, b:type):int =
    var N:int = 0
    for (P : Ps):
        set N += 1
    loop:
        if (D := dup[Ps[0]]):
            break
        else:
            break
    N
V(P:pair(a, b) where a:type, b:type):void =
    if (D := dup[P]):
        Print("dup {D.C}")
        return
    Print("not dup")
K(P:pair(a, b), X:a where a:type, b:type):int =
    R:int = if (D := dup[P]):
        if (D.C > 1) then return 7
        D.C * 10
    else:
        3
    R + 1
Main()<transacts>:void =
    Print("{F(dup(int){A := 5, B := 2}, 9)} {F(pair(int, string){A := 1, B := "x"}, 9)}")
    Print("{G(dup(int){A := 1, B := 2, C := 9})}")
    Print("{G(dup(int){A := 1, B := 2, C := 1})}")
    Print("{G(pair(int, string){A := 1, B := "x"})}")
    Print("{H(array{dup(int){A := 1, B := 2}})}")
    V(dup(int){A := 1, B := 2, C := 3})
    V(pair(int, int){A := 1, B := 2})
    Print("{K(dup(int){A := 1, B := 2, C := 5}, 0)} {K(dup(int){A := 1, B := 2, C := 1}, 0)} {K(pair(int, int){A := 1, B := 2}, 0)}")
    Print("{SR(dup(int){A := 1, B := 2, C := 1})} {SR(dup(int){A := 1, B := 2, C := 5})} {SR(pair(int, int){A := 1, B := 2})}")
    Print("{Loop(dup(int){A := 1, B := 2, C := 3})} {Loop(dup(int){A := 1, B := 2, C := 9})}")
    Print("{Def(dup(int){A := 1, B := 2, C := 4})}")
    Print("{Def(pair(int, int){A := 1, B := 2})}")
    Print("{More(dup(int){A := 1, B := 2, C := 5})} {More(dup(int){A := 1, B := 2, C := 1})}")
    Print("{dup(int){A := 1, B := 2, C := 4}.Try(dup(int){A := 1, B := 2, C := 4})} {dup(int){A := 1, B := 2, C := 4}.Try(dup(int){A := 1, B := 2, C := 3})}")
