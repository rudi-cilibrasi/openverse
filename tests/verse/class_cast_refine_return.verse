# A refining cast's branch with a return (#243): its function returns what to return, and the caller returns it
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b), X:a where a:type, b:type):b =
    if (D := dup[P]):
        return X
    else:
        P.B
Main():void = Print("{F(dup(int){A := 1, B := 2}, 3)}")
