# a tuple expands into a method's, an overloaded or a generic function's parameters, evaluated once (#140)
c := class:
    Base:int = 10
    M(A:int, B:int):int = Base + A + B
    Both(T:tuple(int, int)):int = M(T)
Add(A:int, B:int):int = A + B
Add(A:float, B:float):float = A + B
G(A:t, B:t where t:type):tuple(t, t) = (B, A)
Mk():tuple(int, int) =
    Print("made once")
    (3, 4)
Main():void =
    O := c{}
    T := (1, 2)
    Print("{O.M(T)} {O.Both(T)} {Add(T)} {Add((1.5, 2.5))}")
    P := G(T)
    Print("{P(0)} {P(1)} {O.M(Mk())}")
