# Exclusive paths and refining branches may share a non-failable lazy suffix.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
counter := class:
    var N:int = 0
Lazy(C:counter, N:int)<transacts><decides>:int =
    N >= 0
    set C.N += 1
    N | Lazy[C, N - 1]
Early(N:int):int =
    if (N < 0):
        return 0
    N | N + 1
Refined(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<suspends>:void =
    Sleep(0.0)
    C := counter{}
    var Total:int = 0
    R := for (A := if (D := dup[P]) then (D.C | D.C + 1) else 0, set Total += A,
        B := if (E := dup[Q]) then (E.C | E.C + 1) else 0, set Total += B,
        L := Lazy[C, 1], L = 0):
        Print("refined {A} {B} {Total} {C.N}")
        Total
    Print("end {R.Length} {Total} {C.N}")
Main()<suspends>:void =
    Sleep(0.0)
    C := counter{}
    var Total:int = 0
    R := for (A := Early(0), set Total += A, B := Early(0), set Total += B,
        L := Lazy[C, 1], L = 0):
        Print("exclusive {A} {B} {Total} {C.N}")
        Total
    Print("end {R.Length} {Total} {C.N}")
    Refined(dup(int){A := 1, B := 2}, dup(string){A := "a", B := "b"})
    Refined(dup(int){A := 1, B := 2}, pair(int, string){A := 1, B := "s"})
