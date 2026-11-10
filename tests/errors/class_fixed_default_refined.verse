# expect: 10:52: cannot dispatch Put to class ib yet when a named argument's default computed by code uses an argument at a type, a, that the dispatch refines
# (#142: X is an a where the dispatch is, an int in ib's default)
Tick(S:string, N:int)<transacts>:int =
    Print("tick {S}")
    N
box(t:type) := class:
    Put(X:t, ?C:int = 0)<transacts>:int = C
ib := class(box(int)):
    Put<override>(X:int, ?C:int = Tick("ib", X))<transacts>:int = C
G(B:box(a), X:a where a:type)<transacts>:int = B.Put(X)
Main()<transacts>:void =
    Print("g {G(ib{}, 100)} {G(box(string){}, "s")}")
