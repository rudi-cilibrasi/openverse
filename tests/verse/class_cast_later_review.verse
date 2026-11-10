# Casts as later clauses (#243), the shapes #400's review found: one in an if nested in another's branch,
# an else that declares a name a clause before the cast binds (the else does not see it), two refining
# casts in one condition (one first, one later)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
Nest(P:pair(a, b), Ys:[]int where a:type, b:type):int =
    if (N := Ys[0], M := Ys[1]):
        if (Y := 1, D := dup[P]) then D.C + Y + N else 0
    else:
        -1
ElseNames(P:pair(a, b) where a:type, b:type):int =
    if (Y := 1, D := dup[P]):
        D.C + Y
    else:
        Y := 40
        Y + 2
Two(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type):int =
    if (Y := 1, D := dup[P], E := dup[Q], D.C > Y) then D.C + E.C else -1
TwoFirst(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type):int =
    if (D := dup[P], Y := 1, E := dup[Q]) then D.C + E.C + Y else -1
Main()<transacts>:void =
    Print("{Nest(dup(int){A := 1, B := 2, C := 3}, array{5, 6})}")
    Print("{ElseNames(dup(int){A := 1, B := 2, C := 3})} {ElseNames(pair(int, string){A := 1, B := "x"})}")
    X0 := dup(int){A := 1, B := 2, C := 3}
    Z0 := pair(int, string){A := 1, B := "x"}
    Print("{Two(X0, X0)} {Two(X0, Z0)} {Two(Z0, X0)} {TwoFirst(X0, X0)} {TwoFirst(X0, Z0)} {TwoFirst(Z0, X0)}")
