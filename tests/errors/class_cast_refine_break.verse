# expect: 10:12: the branch of the cast to dup(a), which holds only under a refinement of the type arguments, is compiled as a function of its own, so it cannot have a break that leaves it yet (#243)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b) where a:type, b:type):void =
    loop:
        if (D := dup[P]):
            break
        else:
            break
Main():void = F(dup(int){A := 1, B := 2})
