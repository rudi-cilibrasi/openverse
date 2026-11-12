# expect: (a clause after it, past a generator, uses D in an if with a choice in its branches)
# (#243) a for's clause past a generator after a refining cast that uses its
# name in a branch of an if with a choice there: the if keeps its branches'
# values, so the cast is not cast again inside them
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    Items:[]t = array{}
    C:int = 1
Br(P:pair(a, b), N:int where a:type, b:type):[]int =
    for (D := dup[P], X : D.Items, Y := (if (N > 0) then (D.C | 10) else 0)) { Y }
Main():void =
    Y:pair(int, int) = dup(int){A := 7, B := 8, Items := array{5, 6}, C := 2}
    Print("{Br(Y, 1).Length} {Br(Y, 0).Length}")
