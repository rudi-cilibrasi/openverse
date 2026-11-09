# expect: 9:8: the branch of the cast to dup(a), which holds only under a refinement of the type arguments, is compiled as a function of its own, so it cannot have a return yet (#243)
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
