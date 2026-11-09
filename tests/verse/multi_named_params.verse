# Functions with several values and named parameters (#283): inlined, the
# arguments bound as at any call (positional, then named as written, then
# the defaults of those omitted, each seeing the parameters before it)
G(S : string, V : int)<transacts>:int =
    Print(S)
    V
F(A : int, ?B : int = A * 10, ?C : int = G("dc", 7))<transacts>:int = (A | B) + C
Chain(A : int, ?B : int = A + 1, ?C : int = B * 2)<transacts>:int = A | B | C
Arr : []int = array{1, 2}
Dec(A : int, ?B : int = Arr[A])<decides><transacts>:int = A | B
Tup(A : int, B : int, ?C : int = 0)<transacts>:int = A | B | C
Main()<transacts>:void =
    for (X := F(1)):
        Print("{X}")
    for (X := F(G("a", 2), ?C := G("c", 0), ?B := G("b", 5))):
        Print("{X}")
    # (the positional choice first: the omitted default once per alternative)
    for (X := F(?B := 3, 1 | 2)):
        Print("{X}")
    if (X := F(1, ?C := 0), X > 5):
        Print("if {X}")
    for (X := Chain(1)):
        Print("chain {X}")
    for (X := Chain(1, ?B := 5)):
        Print("chain b {X}")
    # (a default that fails fails the call of a <decides> one)
    for (X := Dec[1]):
        Print("dec {X}")
    for (X := Dec[5]):
        Print("never {X}")
    # two sites: each its own default
    for (X := F(1, ?C := 0), Y := F(2, ?B := 3)):
        Print("{X} {Y}")
    # one tuple argument to the positional parameters, as at a call
    for (X := Tup((1, 2))):
        Print("tup {X}")
