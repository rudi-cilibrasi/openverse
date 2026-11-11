# A refining cast's branch that suspends (#243): its function <suspends>, the dispatch a suspends call
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
