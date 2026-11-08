# a result type whose initial value nests deeply (#198)
c0(t:type) := class:
    X:c1(t)
c1(t:type) := class:
    X:c2(t)
c2(t:type) := class:
    X:c3(t)
c3(t:type) := class:
    X:c4(t)
c4(t:type) := class:
    X:c5(t)
c5(t:type) := class:
    X:c6(t)
c6(t:type) := class:
    X:c7(t)
c7(t:type) := class:
    X:c8(t)
c8(t:type) := class:
    X:c9(t)
c9(t:type) := class:
    X:c10(t)
c10(t:type) := class:
    X:c11(t)
c11(t:type) := class:
    X:c12(t)
c12(t:type) := class:
    X:c13(t)
c13(t:type) := class:
    X:c14(t)
c14(t:type) := class:
    V:t
pair(a:type, b:type) := class:
    A:a
    B:b
    Wrap(C:c0(b))<suspends>:c0(b) = C
ipair(b:type) := class(pair(int, b)):
    Wrap<override>(C:c0(b))<suspends>:c0(b) =
        Sleep(0.1)
        C
G(P:pair(a, b), Arr:[]c0(b) where a:type, b:type)<suspends>:int =
    if (C := Arr[0]):
        D := P.Wrap(C)
        Sleep(0.1)
        1
    else:
        0
Main()<suspends>:void =
    Print("{G(ipair(int){A := 1, B := 2}, array{})}")
