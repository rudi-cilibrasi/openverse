# expect: a sink(int) is never an ib: no class below both gives sink those type arguments, so ib[…] would always fail
# a cast from a reference through views that no class below can pass
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u):int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Get<override>():t = V
    Put<override>(X:u):int = 1
ib := class(both(int, string)):
    Put<override>(X:string):int = 2
Main():void =
    U:sink(int) = both(string, int){V := "s"}
    if (B := ib[U]) then Print("ib") else Print("not ib")
