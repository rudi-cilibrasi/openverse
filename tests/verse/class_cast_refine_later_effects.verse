# A cast that refines type arguments as a later clause of an if's condition,
# after clauses with effects (#243): it takes the clauses after it as its
# branch in a clause of its own, so that their failure, or its own, undoes
# the whole condition, output included; the then-branch, which uses the
# cast's name, casts the object again, typed under the refinement, and sees
# the names the clauses after the cast bind; a second cast there, of a
# parameter, it casts again too.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
cell := class:
    var N:int = 0
Bump(H:cell, K:int)<transacts><decides>:int =
    K > 0
    set H.N += K
    K
# the branch's value at the type the refinement gives
Second(H:cell, P:pair(a, b) where a:type, b:type)<transacts>:?b =
    if (M := Bump[H, 1], Print("m{M}"), D := dup[P], X := D.A, D.C > M) then option{X} else false
# a statement if, its branch setting a var; the names after the cast
Count(H:cell, P:pair(a, b), Min:int where a:type, b:type)<transacts>:int =
    var Total:int = 0
    if (set H.N += 10, D := dup[P], Y := D.C + 1, Y > Min):
        set Total = Y * 100 + H.N
    Total
# a bare cast, and a branch that uses neither it nor what follows it
Test(H:cell, P:pair(a, b) where a:type, b:type)<transacts>:string =
    if (set H.N += 1000, dup[P]) then "dup {H.N}" else "not {H.N}"
# two casts after the Print: the branch takes both refinements
Two(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<transacts>:?tuple(b, d) =
    if (Print("t"), D := dup[P], E := dup[Q]) then option{(D.A, E.A)} else false
# a return from the then-branch
Ret(H:cell, P:pair(a, b) where a:type, b:type)<transacts>:int =
    if (Print("r"), D := dup[P]):
        return D.C
    -1
Main()<transacts>:void =
    H := cell{}
    Y:pair(int, int) = dup(int){A := 1, B := 2}
    Z:pair(int, string) = pair(int, string){A := 1, B := "s"}
    if (V := Second(H, Y)?) then Print("Second {V} {H.N}")
    if (V := Second(H, Z)?) then Print("Second {V}") else Print("Second no {H.N}")
    Print("Count {Count(H, Y, 3)} {Count(H, Y, 5)} {Count(H, Z, 0)} {H.N}")
    Print("Test {Test(H, Y)} {Test(H, Z)}")
    Print("Ret {Ret(H, Y)} {Ret(H, Z)}")
    Q:pair(string, string) = dup(string){A := "q", B := "r"}
    if (V := Two(Y, Q)?) then Print("Two {V(0)} {V(1)}")
    if (V := Two(Y, Z)?) then Print("Two") else Print("Two no")
