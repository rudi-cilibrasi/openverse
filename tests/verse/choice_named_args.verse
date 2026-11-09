# Choices inside named arguments (#283): lifted after the positional
# arguments, in the order written, as a call evaluates them; the defaults
# of those omitted run after
F(A : int, ?B : int = 0, ?C : int = 0)<transacts>:int = A * 100 + B * 10 + C
G(S : string, V : int)<transacts>:int =
    Print(S)
    V
D()<transacts>:int =
    Print("d")
    9
H(A : int, ?B : int = D())<transacts>:int = A * 10 + B
Main()<transacts>:void =
    for (X := F(1, ?B := 1 | 2)):
        Print("{X}")
    # named as written, after the positional ones
    for (X := F(G("a", 1), ?C := G("c", 3), ?B := G("b", 2) | 5)):
        Print("{X}")
    # a positional written after a named one is evaluated first
    for (X := F(?C := G("c", 3), 1 | 2)):
        Print("{X}")
    # an omitted default runs after the arguments, so after the choice
    for (X := H(1 | 2)):
        Print("{X}")
    for (X := H(G("a", 1), ?B := 3 | 4)):
        Print("{X}")
    if (X := F(1, ?B := 1 | 2 | 3), X > 115):
        Print("if {X}")
