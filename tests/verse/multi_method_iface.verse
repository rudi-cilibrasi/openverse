# Interface methods with several values (#283): a call through the
# interface dispatches on the receiver's class, as for overridden methods
# (#328), an exclusive choice of the implementations
shape := interface:
    Sides(K : int)<transacts>:int
named := interface(shape):
    Name()<transacts>:string
tri := class(named):
    Sides<override>(K : int)<transacts>:int = 3 * K | 30 * K
    Name<override>()<transacts>:string = "tri" | "triangle"
    Both()<transacts>:int = Sides(1) + 100
sq := class(shape):
    Sides<override>(K : int)<transacts>:int = 4 * K
rsq := class(sq):
    Sides<override>(K : int)<transacts>:int = (Print("r"); 40 * K) | 41 * K
Main()<transacts>:void =
    Ss : []shape = array{tri{}, sq{}, rsq{}}
    for (S : Ss, N := S.Sides(2)):
        Print("a {N}")
    Ns : []named = array{tri{}}
    for (X : Ns, M := X.Name()):
        Print("b {M}")
    T := tri{}
    for (N := T.Sides(1)):
        Print("c {N}")
    for (N := T.Both()):
        Print("d {N}")
    if (S := Ss[2], N := S.Sides(1), N > 40):
        Print("e {N}")
