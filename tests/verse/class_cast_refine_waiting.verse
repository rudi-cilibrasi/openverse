# In a <suspends> function (#243): a refining cast in a for's clauses after
# one that prints, the body, which casts again, waiting; and an if whose
# else gives no value, Err(), its branch setting a var from outside it and
# waiting, the copy-out tuple typed by the branch's own value.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
Wait(N:int)<suspends>:int =
    Sleep(0.01)
    N
Sum(Ps:[]pair(a, b) where a:type, b:type)<suspends>:int =
    var S:int = 0
    for (P : Ps, (Print("s"); true?), D := dup[P]):
        set S += Wait(D.C)
    S
One(P:pair(a, b) where a:type, b:type)<suspends>:int =
    var S:int = 0
    if (D := dup[P]) then (set S += Wait(D.C)) else Err()
    S
Main()<suspends>:void =
    Y:pair(int, int) = dup(int){A := 1, B := 2}
    Z:pair(int, int) = pair(int, int){A := 3, B := 4}
    Print("Sum {Sum(array{Y, Z, Y})}")
    Print("One {One(Y)}")
