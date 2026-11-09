# expect: 10:8: the else of the cast to dup(a), which holds only under a refinement of the type arguments, cannot suspend yet
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b), X:a where a:type, b:type)<suspends>:b =
    if (D := dup[P]):
        X
    else:
        Sleep(0.1)
        P.B
Main()<suspends>:void = Print("{F(dup(int){A := 1, B := 2}, 7)}")
