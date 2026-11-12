# Overloaded methods with several values (#283): of a generic class, with named parameters and
# defaults (a default seeing the fields), one calling another list through another receiver and bare;
# and lists that call their method's own name: another list, and the same one recursively (taken
# lazily, as a generator)
box(t:type) := class:
    A : t
    B : t
    Both()<transacts>:t = A | B
    Both(X : t, Y : t, ?Also : t = A)<transacts>:t = X | Y | Also
    Both(N : int, M : int, K : int, L : int)<transacts>:int = N + M + K + L
    Swap(Other : box(t))<transacts>:t = Other.Both() | Both(B, Other.A)
counter := class:
    K : int = 2
    Vals()<transacts>:int = K | K * 10
    Vals(X : int)<transacts>:int = X | Vals()
    Count(N : int)<transacts>:int = if (N <= 0) then 0 else (N | Count(N - 1))
    Count()<transacts>:int = Count(K) + 100
Main()<transacts>:void =
    X := box(string){A := "p", B := "q"}
    for (V := X.Both()) { Print("v {V}") }
    for (V := X.Both("r", "s")) { Print("w {V}") }
    for (V := X.Both("r", "s", ?Also := "z")) { Print("u {V}") }
    Print("n {X.Both(1, 2, 3, 4)}")
    I := box(int){A := 1, B := 2}
    for (V := I.Both()) { Print("i {V}") }
    for (V := I.Both(5, 6)) { Print("j {V}") }
    for (V := X.Swap(box(string){A := "m", B := "n"})) { Print("s {V}") }
    if (V := I.Both(7, 8), V > 7) then Print("f {V}")
    C := counter{}
    for (V := C.Vals(5)) { Print("c {V}") }
    for (V := C.Count(3)) { Print("k {V}") }
    for (V := C.Count()) { Print("m {V}") }
