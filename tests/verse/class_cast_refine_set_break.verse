# A refining cast's branch that sets a var from outside it and breaks out (#243): the var is set before the loop is left
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
            break
        else:
            break
    N
Main():void = Print("{F(dup(int){A := 1, B := 2})}")
