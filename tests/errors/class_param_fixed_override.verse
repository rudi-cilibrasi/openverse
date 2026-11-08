# expect: dup repeats type arguments that pair leaves open, or fixes them to types that mention type parameters, so it cannot override Get
pair(t:type, u:type) := class:
    A:t
    B:u
    Get():t = A
dup(t:type) := class(pair(t, t)):
    Get<override>():t = B
Main():void = Print("x")
