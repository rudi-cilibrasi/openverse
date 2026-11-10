# Overloaded functions with several values (#283), from the reviews: an
# overload with one value whose body calls a function with several values
# (inlined as any body), a helper calling the overloaded one where the
# first success is taken (with the overload of several values or of one),
# a class block, and an if with no filter
G(N:int):int = N | N + 1
F(N:int):int = N | N * 10
F(S:string):[]int = for (X := G(S.Length)) { X }
Two(N:int):int = N * 2
Two(S:string):int = S.Length | 100
H(S:string):int = Two(S) + 1
H2(N:int):int = Two(N) + 1
c := class:
    K : int = 3
    block:
        for (X := F(K)) { Print("blk {X}") }
Main():void =
    for (X := F(2)) { Print("a {X}") }
    for (X : F("ab")) { Print("b {X}") }
    if (Y := H("abc"), Y > 50) then Print("c {Y}") else Print("none")
    if (Y := H2(3), Y > 5) then Print("d {Y}") else Print("none")
    if (Z := option{H("x")}, V := Z?) then Print("e {V}")
    if (W := Two("q")) then Print("f {W}")
    O := c{}
    Print("g {O.K}")
