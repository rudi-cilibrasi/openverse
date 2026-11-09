# Methods with several values (#283), from the review of #310: a field in a
# bare call's argument is the field, not a top-level name; (super:) calls
# it; one tuple argument is spread over the parameters, as at a method's call
K : int = 100
c := class:
    K : int
    Add(A : int)<transacts>:int = A + 1
    Vals()<transacts>:int = Add(K) | K
    Pair(A : int, B : int)<transacts>:int = A + K | B + K
    Other()<transacts>:int = 0
sub := class(c):
    Other<override>()<transacts>:int =
        var S : int = 0
        for (X := (super:)Vals()):
            set S += X
        S
Main()<transacts>:void =
    for (X := c{K := 5}.Vals()):
        Print("{X}")
    Print("{sub{K := 10}.Other()}")
    T := (1, 2)
    for (X := c{K := 100}.Pair(T)):
        Print("{X}")
    for (X := c{K := 100}.Pair((5, 6))):
        Print("{X}")
