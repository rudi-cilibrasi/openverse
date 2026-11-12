# A cast that refines type arguments as a clause of a for (#243): it takes
# the clauses after it, up to the next generator, as its branch, in a clause
# of its own, which fails for an element whose class is not the cast's, and
# undoes what that element's clauses did; the body, which uses the cast's
# name and the names those clauses bind, casts the object again.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
fixl(u:type) := class(pair(int, u)):
    D:int = 7
cell := class:
    var N:int = 0
# a filter after the generator; the body's value under the refinement
Bs(Ps:[]pair(a, b) where a:type, b:type):[]b =
    for (P : Ps, D := dup[P]):
        D.A
# clauses with effects before and after it, names after it in the body
Fx(H:cell, Ps:[]pair(a, b) where a:type, b:type)<transacts>:[]int =
    for (P : Ps, Print("p"), set H.N += 1, F := fixl[P], Y := F.D + F.A, F.A > 0, var Z:int = Y):
        set Z += 1
        set H.N += 100
        Z + F.A
# the cast before a generator that does not use it
Grid(P:pair(a, b) where a:type, b:type):[]int =
    for (D := dup[P], X := 1..3):
        D.C * 10 + X
# a bare cast, a test; and a return from the body
First(Ps:[]pair(a, b) where a:type, b:type):int =
    for (P : Ps, dup[P], Q := dup[P]):
        if (Q.C > 3) then return Q.C
    -1
Show(Xs:[]int):string =
    var S:string = ""
    for (X : Xs) { set S = "{S}{X}," }
    S
Main()<transacts>:void =
    H := cell{}
    Y:pair(int, int) = dup(int){A := 1, B := 2}
    Z:pair(int, int) = pair(int, int){A := 5, B := 6}
    W:pair(int, int) = fixl(int){A := 3, B := 0}
    V:pair(int, int) = fixl(int){A := 0, B := 0}
    Print("Bs {Show(Bs(array{Y, Z, Y}))}")
    Print("Fx {Show(Fx(H, array{Y, W, Z, V, W}))} {H.N}")
    Print("Grid {Show(Grid(Y))} {Show(Grid(Z))}")
    Print("First {First(array{Z, Y})} {First(array{Z, Z})}")
