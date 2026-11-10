# A computed default (#142) of a class that fixes type arguments, called from generic code: its own
Tick(S:string)<transacts>:int =
    Print("tick {S}")
    7
box(t:type) := class:
    Put(X:t, ?N:int = Tick("box"))<transacts>:int = N
ib := class(box(int)):
    Put<override>(X:int, ?N:int = Tick("ib") + 1)<transacts>:int = N + X
G(B:box(a), X:a where a:type)<transacts>:int = B.Put(X)
Main()<transacts>:void =
    Print("{G(ib{}, 100)} {G(box(string){}, "s")}")
