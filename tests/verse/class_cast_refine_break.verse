# A refining cast's branch with a break that leaves it (#243): its function returns that it broke, and the caller breaks
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
