# expect: which a cast gives only as a clause of a failure context
# (#243) a refining cast outside a failure context, which it would fail
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
Use(P:pair(a, b) where a:type, b:type):int =
    D := dup[P]
    D.C
Main():void = Print("{Use(dup(int){A := 1, B := 2})}")
