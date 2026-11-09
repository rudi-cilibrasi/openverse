# expect: 8:20: the branch of the cast to dup(a), which holds only under a refinement of the type arguments, is compiled as a function of its own, so it cannot suspend yet
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b), X:a where a:type, b:type)<suspends>:b =
    if (D := dup[P]):
        Sleep(0.1)
        X
    else:
        P.B
Main()<suspends>:void = Print("{F(dup(int){A := 1, B := 2}, 7)}")
