# Generic captures and results share the continuation after each choice.
# Filters reduce each sequence to one result; emitting it must stay small.
Two(N:int):int = N | N + 1
Early(N:int):int =
    if (N < 0):
        return 0
    N | N + 1
Composed(I:t where t:type):[]t =
    for (A0 := (Two(0) | Two(2)), A0 = 0,
        A1 := (Two(0) | Two(2)), A1 = 0,
        A2 := (Two(0) | Two(2)), A2 = 0,
        A3 := (Two(0) | Two(2)), A3 = 0,
        A4 := (Two(0) | Two(2)), A4 = 0,
        A5 := (Two(0) | Two(2)), A5 = 0,
        A6 := (Two(0) | Two(2)), A6 = 0,
        A7 := (Two(0) | Two(2)), A7 = 0,
        A8 := (Two(0) | Two(2)), A8 = 0,
        A9 := (Two(0) | Two(2)), A9 = 0,
        A10 := (Two(0) | Two(2)), A10 = 0,
        A11 := (Two(0) | Two(2)), A11 = 0,
        A12 := (Two(0) | Two(2)), A12 = 0,
        A13 := (Two(0) | Two(2)), A13 = 0) { I }
Exclusive(I:t where t:type):[]t =
    for (A0 := Early(0), A0 = 0,
        A1 := Early(0), A1 = 0,
        A2 := Early(0), A2 = 0,
        A3 := Early(0), A3 = 0,
        A4 := Early(0), A4 = 0,
        A5 := Early(0), A5 = 0,
        A6 := Early(0), A6 = 0,
        A7 := Early(0), A7 = 0,
        A8 := Early(0), A8 = 0,
        A9 := Early(0), A9 = 0,
        A10 := Early(0), A10 = 0,
        A11 := Early(0), A11 = 0,
        A12 := Early(0), A12 = 0,
        A13 := Early(0), A13 = 0) { I }
counter := class:
    var N:int = 0
Step(H:counter, Label:string, N:int)<transacts>:int =
    Print("{Label}{N}")
    set H.N += N
    N | N + 1
Effects(X:t, Y:t, Required:int where t:subtype(comparable))<transacts>:void =
    H := counter{}
    var Current:t = X
    R := for (A := (Step(H, "a", 0) | Step(H, "a", 2)), (set Current = Y; true?), A = Required,
        B := (Step(H, "b", 10) | Step(H, "b", 20)), B = 10):
        set H.N += 100
        Current
    if (V := R[0]) then Print("found {R.Length} {H.N}") else Print("empty {H.N}")
    if (Current = Y):
        Print("copied")
    else:
        Print("original")
EmptyInts():[]int = array{}
LateEmpty(X:t, Y:t where t:subtype(comparable))<transacts>:void =
    H := counter{}
    var Current:t = X
    R := for (A := (Step(H, "a", 0) | Step(H, "a", 2)), A = 0, (set Current = Y; true?),
        B : EmptyInts(), C := (Two(10) | Two(20))) { Current }
    if (Current = Y) then Print("kept {R.Length} {H.N}") else Print("lost")
Fails(X:t where t:type)<transacts><decides>:[]t =
    for (A := (Two(0) | Two(2)), B := (Two(10) | Two(20))):
        Print("failed body")
        false?
        X
box(t:type) := class:
    X:t
    Y:t
    Values():[]t =
        var Current:t = X
        for (A := (Two(0) | Two(2)), A = 0, (set Current = Y; true?),
            B := (Two(10) | Two(20)), B = 10) { Current }
Main()<transacts>:void =
    A := Composed(7)
    if (V := A[0]) then Print("composed {A.Length} {V}")
    B := Composed("s")
    if (V := B[0]) then Print("composed {B.Length} {V}")
    C := Exclusive(8)
    if (V := C[0]) then Print("exclusive {C.Length} {V}")
    D := Exclusive("t")
    if (V := D[0]) then Print("exclusive {D.Length} {V}")
    Effects(1, 2, 0)
    Effects(1, 2, 9)
    LateEmpty(1, 2)
    if (R := Fails[1]) then Print("unexpected {R.Length}") else Print("body failed")
    X := box(string){X := "before", Y := "after"}.Values()
    if (V := X[0]) then Print("method {X.Length} {V}")
