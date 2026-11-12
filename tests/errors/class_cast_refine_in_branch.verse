# expect: which a cast gives only as a clause of a failure context
# (#243) a refining cast in a branch of an if outside any failure context,
# where it could not fail: the if is no failure context, only its condition
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
Use(P:pair(a, b), N:int where a:type, b:type):int = if (N > 0) then dup[P].C else 0
Main():void = Print("{Use(dup(int){A := 1, B := 2}, 1)}")
