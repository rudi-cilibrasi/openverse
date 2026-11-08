# expect: type parameter t of nest occurs only inside the type arguments nest gives its parent
pair(t:type, u:type) := class:
    A:t
    B:u
    Get():t = A
nest(t:type) := class(pair(?t, ?t)):
    Get<override>():?t = B
Main():void = Print("x")
