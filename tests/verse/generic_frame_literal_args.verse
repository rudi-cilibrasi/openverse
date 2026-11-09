# literal arguments (an empty array, an empty option) of generic suspends
# callees, from generic and closed callers, under a branch, in a sync arm, and
# at a generic override dispatched to under a refinement: a generic callee is
# arrived at through its `arrive`, a plain call that checks each argument
# against its parameter's type (#256)
F(X:t, A:[]t, O:?t where t:type)<suspends>:int =
    Sleep(0.1)
    if (O?) then A.Length + 10 else A.Length
G(X:t where t:type)<suspends>:int =
    branch:
        Sleep(0.5)
    F(X, array{}, false) + F(X, array{X}, option{X})
H(X:t where t:type)<suspends>:int =
    S := sync:
        F(X, array{}, false)
        F(X, array{X, X}, false)
    S(0) + S(1)
pair(a:type, b:type) := class:
    A:a
    B:b
    Both(X:[]b, O:?b)<suspends>:int = X.Length
ipair(b:type) := class(pair(int, b)):
    Both<override>(X:[]b, O:?b)<suspends>:int =
        Sleep(0.2)
        X.Length + 100
U(P:pair(a, b) where a:type, b:type)<suspends>:int = P.Both(array{}, false)
Main()<suspends>:void =
    Print("{G(1)} {H("s")} {F(2, array{}, false)}")
    Print("{U(ipair(string){A := 1, B := "x"})} {U(pair(int, int){A := 1, B := 2})}")
