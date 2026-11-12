# A cast that refines type arguments as a statement of a <decides> body
# (#243): the rest of the body is its branch, typed under the refinement,
# and its failure, or the cast's, the call's, which undoes what the body did
# before the cast (output included), as any failure context does.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
fixl(u:type) := class(pair(int, u)):
    D:int = 7
cell := class:
    var N:int = 0
Bump(H:cell, K:int)<transacts><decides>:int =
    K > 0
    set H.N += K
    K
# b = a under the refinement: D.A is a b
SameB(P:pair(a, b) where a:type, b:type)<decides>:b =
    D := dup[P]
    D.A
# a = int under it: an int is an a
FixA(P:pair(a, b) where a:type, b:type)<decides>:a =
    F := fixl[P]
    F.D + F.A
# effects before and after the cast, undone when it, or a clause after it, fails
Fx(H:cell, P:pair(a, b), Min:int where a:type, b:type)<transacts><decides>:int =
    M := Bump[H, 1]
    Print("before")
    D := dup[P]
    Print("after")
    set H.N += 10
    D.C > Min
    D.C + M
# a bare cast, a test; the cast as the body's value
IsDup(P:pair(a, b) where a:type, b:type)<decides>:void =
    dup[P]
AsDup(P:pair(a, b) where a:type, b:type)<decides>:dup(a) =
    dup[P]
# a second cast in the first's branch, of a value the first gives
Twice(P:pair(a, b) where a:type, b:type)<decides>:b =
    D := dup[P]
    Q:pair(b, a) = dup(b){A := D.B, B := D.A, C := D.C + 1}
    E := dup[Q]
    E.A
# a return in the branch
Early(P:pair(a, b), N:int where a:type, b:type)<decides>:int =
    D := dup[P]
    if (N > 0) then return N + D.C
    D.C
# in a method: Self's members in the branch
box(t:type) := class:
    P:pair(t, int)
    K:int = 100
    Get()<decides>:t =
        D := dup[P]
        D.A + K - K
Main()<transacts>:void =
    H := cell{}
    Y:pair(int, int) = dup(int){A := 1, B := 2}
    Z:pair(int, string) = pair(int, string){A := 1, B := "s"}
    W:pair(int, string) = fixl(string){A := 3, B := "w"}
    if (V := SameB[Y]) then Print("SameB {V}")
    if (V := SameB[Z]) then Print("SameB {V}") else Print("SameB no")
    if (V := FixA[W]) then Print("FixA {V}")
    if (V := FixA[Z]) then Print("FixA {V}") else Print("FixA no")
    if (V := Fx[H, Y, 3]) then Print("Fx {V} {H.N}")
    if (V := Fx[H, Y, 5]) then Print("Fx {V}") else Print("Fx no {H.N}")
    if (V := Fx[H, Z, 0]) then Print("Fx {V}") else Print("Fx no {H.N}")
    if (IsDup[Y], not IsDup[Z]) then Print("IsDup")
    if (D := AsDup[Y]) then Print("AsDup {D.C}")
    if (V := Twice[Y]) then Print("Twice {V}")
    if (V := Early[Y, 1]) then Print("Early {V}")
    if (V := Early[Y, 0]) then Print("Early {V}")
    if (V := Early[Z, 1]) then Print("Early {V}") else Print("Early no")
    if (V := box(int){P := dup(int){A := 9, B := 9}}.Get[]) then Print("Get {V}")
    if (V := box(int){P := pair(int, int){A := 9, B := 9}}.Get[]) then Print("Get {V}") else Print("Get no")
