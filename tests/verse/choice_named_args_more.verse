# Choices inside named arguments (#283): a generic function, a method
# dispatched to its override (with its own default), and a block and a
# construction as named arguments
Pick(A : t, ?B : t, ?C : logic = false where t : type)<transacts>:t = if (C?) then B else A
base := class:
    K : int
    M(A : int, ?B : int = 1)<transacts>:int = K + A * B
sub := class(base):
    M<override>(A : int, ?B : int = 2)<transacts>:int = K + A * B * 100
pt := struct { X : int; Y : int }
Add(A : int, ?X : int = 0)<transacts>:int = A + X
F(?P : pt, ?K : int = 1)<transacts>:int = (P.X + P.Y) * K
Main()<transacts>:void =
    for (X := Pick(1, ?B := 10 | 20, ?C := true | false)):
        Print("{X}")
    Os : []base = array{base{K := 0}, sub{K := 0}}
    for (O : Os, X := O.M(1, ?B := 3 | 4)):
        Print("{X}")
    for (X := F(?K := block{ A := 1 | 2; A }, ?P := pt{Y := 10 | 20, X := 0})):
        Print("{X}")
    # in a comparison chain (this hung on main: the call was refused, then
    # lifted again and again)
    for (B := (Add(?X := 1, 2 | 3) < 5)):
        Print("ok")
    if (Add(?X := 1, 2 | 3) > 3):
        Print("gt")
