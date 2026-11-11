meter := class:
    var N:int = 0
box(t:type) := class:
    H:meter
    A:t
    Both()<transacts>:t = A | A
fixed := class(box(int)):
    Both<override>()<transacts>:int =
        set H.N += 10
        Print("fixed {H.N}")
        1 | 2 | 3
Run(P:box(t) where t:type)<transacts><decides>:void =
    for (V := P.Both()):
        set P.H.N += 1
        Print("body {P.H.N}")
        P.H.N < 12
Main()<transacts><decides>:void =
    H := meter{}
    Run[fixed{H:=H,A:=0}]
    Print("unreachable")
