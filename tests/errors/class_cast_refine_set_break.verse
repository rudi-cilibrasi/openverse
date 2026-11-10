# expect: 13:12: the branch of the cast to dup(a), which holds only under a refinement of the type arguments, is compiled as a function of its own, so it cannot both set a var from outside it and have a break that leaves it yet (#243)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
F(P:pair(a, b) where a:type, b:type):int =
    var N:int = 0
    loop:
        if (D := dup[P]):
            set N = D.C
            # (the break would skip setting N after the if)
            break
        else:
            break
    N
Main():void = Print("{F(dup(int){A := 1, B := 2})}")
