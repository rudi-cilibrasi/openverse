# An interface's default implementation of a method with several values
# (#283): the alternative of the dispatch for the classes that have none of
# their own, as a class's own implementation is (#328, #372)
P(S : string)<transacts>:int =
    Print(S)
    1
shape := interface:
    Base : int = 10
    Sides()<transacts>:int = Base | Base + 1
    Twice()<transacts>:int = Sides() * 2
deep := interface(shape):
    Name()<transacts>:string = "deep" | "deeper"
tri := class(shape):
    Sides<override>()<transacts>:int = 3 | (super:)Sides() + 100
blob := class(deep):
    Base<override> : int = 20
kid := class(blob):
    Sides<override>()<transacts>:int = (P("k"); 7) | 8
Main()<transacts>:void =
    Ss : []shape = array{tri{}, blob{}, kid{}}
    for (S : Ss, N := S.Sides()):
        Print("a {N}")
    for (S : Ss, N := S.Twice()):
        Print("b {N}")
    Ds : []deep = array{blob{}, kid{}}
    for (D : Ds, M := D.Name()):
        Print("c {M}")
    if (S := Ss[2], N := S.Sides(), N > 7):
        Print("d {N}")
