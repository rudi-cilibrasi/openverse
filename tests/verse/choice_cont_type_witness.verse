# Type-only captures retain their witnesses in shared continuations.
Two(N:int):int = N | N + 1
First(Unused:t where t:type):int =
    if (A0 := (Two(0) | Two(2)), A0 = 0,
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
        A13 := (Two(0) | Two(2)), A13 = 0, E:[]t = array{}, E.Length = 0) then A0 else -1
All(Unused:t where t:type):int =
    R := for (A0 := (Two(0) | Two(2)), A0 = 0,
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
        A13 := (Two(0) | Two(2)), A13 = 0):
        E:[]t = array{}
        E.Length
    R.Length

Shape(Unused:t, Key:u where t:type, u:subtype(comparable)):int =
    if (A := (Two(0) | Two(2)), A = 0, B := (Two(10) | Two(20)), B = 10,
        Empty:[]?t = array{}, M:[u]t = map{}, Fns:[]type{_(:t):t} = array{},
        Empty.Length + M.Length + Fns.Length = 0):
        A + B
    else:
        -1
ReturnEmpty(Unused:t where t:type):[]?t =
    if (A := (Two(0) | Two(2)), A = 0, B := (Two(10) | Two(20)), B = 10, Empty:[]?t = array{}):
        Empty
    else:
        array{}
counter := class:
    var N:int = 0
Touch(H:counter, N:int)<transacts>:int =
    set H.N += N
    N | N + 1
State(Unused:t where t:type)<transacts>:int =
    H := counter{}
    var Total:int = 0
    if (A := (Touch(H, 1) | Touch(H, 3)), set Total += A,
        B := (Touch(H, 10) | Touch(H, 20)), Empty:[]t = array{},
        Empty.Length = 0, A + B > 23):
        Print("state {A} {B} {Total} {H.N}")
    else:
        Print("miss {Total} {H.N}")
    Total
box(t:type) := class:
    V:t
    Size():int =
        R := for (A := (Two(0) | Two(2)), A = 0, B := (Two(10) | Two(20)), B = 10):
            Empty:[]t = array{}
            Empty.Length
        R.Length
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)) {}
Refined(P:pair(a, b) where a:type, b:type):int =
    if (D := dup[P]):
        if (A := (Two(0) | Two(2)), A = 0, B := (Two(10) | Two(20)), B = 10,
            Empty:[]a = array{}, Other:[]b = array{}):
            Empty.Length + Other.Length + 1
        else:
            -1
    else:
        0
expr(t:type) := class {}
parts(a:type, b:type) := class(expr(tuple(a, b))):
    L:a
    R:b
Opened(P:expr(t) where t:type):int =
    if (D := parts[P]):
        R := for (A := (Two(0) | Two(2)), A = 0, B := (Two(10) | Two(20)), B = 10):
            Empty:[]t = array{}
            Empty.Length
        R.Length
    else:
        0
Dup(X:t where t:type):t = X | X
Inline(Unused:t where t:type):[]t =
    K := 0 | 1
    if (A := (Two(0) | Two(2)), A = 0, B := (Two(10) | Two(20)), B = 10, Empty:[]t = array{}):
        Empty
    else:
        array{}
InlineTriple(X:a, Y:b, Z:c where a:type, b:type, c:type):[]b =
    K := 0 | 1
    if (A := (Two(0) | Two(2)), A = 0, B := (Two(10) | Two(20)), B = 10,
        E1:[]a = array{}, E2:[]b = array{}, E3:[]c = array{}):
        E2
    else:
        array{}
Main()<transacts>:void =
    Print("first {First(7)} {First("s")}")
    Print("all {All(7)} {All("s")}")
    Print("shape {Shape(7, "key")}")
    Print("result {ReturnEmpty("s").Length}")
    Print("total {State("s")}")
    Print("method {box(string){V := "s"}.Size()}")
    Print("class {First(box(string){V := "s"})} {All(box(int){V := 7})}")
    Print("refined {Refined(dup(int){A := 1, B := 2})}")
    Print("opened {Opened(parts(int, string){L := 1, R := "s"})}")
    # The same inlined suffix is checked at two closed instances.
    for (V := (Dup(1) | Dup("s")), Empty := Inline(V)):
        Print("instance {Empty.Length}")
    # Repeated types must retain which alias each one instantiates.
    for (V := (Dup((1, 2, "s")) | Dup((1, "s", "s"))), Empty := InlineTriple(V(0), V(1), V(2))):
        Print("aliases {Empty.Length}")
