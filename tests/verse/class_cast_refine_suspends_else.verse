# A refining cast whose else suspends (#243): the dispatch a suspends call, as when the branch does
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
