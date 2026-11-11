container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u, ?N:int = 0):int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    F:int = 4
    Get<override>():t = V
    Put<override>(X:u, ?N:int = F):int = N
Main():void =
    S:sink(string) = both(int, string){V := 1}
    Print("{S.Put("x")}")
