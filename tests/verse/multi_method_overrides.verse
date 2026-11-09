# Methods with several values that are overridden (#283): each
# implementation a function of its own; a call dispatches on the receiver's
# class through guarded alternatives (one runs: its class, and no class
# below it that implements the method again); (super:) calls the one above
shape := class:
    K : int
    Sizes()<transacts>:int = K | K + 1
    Name()<transacts>:string = "shape"
square := class(shape):
    Sizes<override>()<transacts>:int = K * 10 | K * 20 | K * 30
big := class(square):
    Sizes<override>()<transacts>:int = 1000
circle := class(shape):
    Name<override>()<transacts>:string = "circle"
base := class:
    K : int
    var N : int = 0
    Vals(?D : int = 1)<transacts>:int = K | K + D
    Twice()<transacts>:int = Vals() * 2
sub := class(base):
    Vals<override>(?D : int = 100)<transacts>:int =
        set N += 1
        (super:)Vals(?D := D) | -1
abs := class<abstract>:
    Get()<transacts>:int
one := class(abs):
    Get<override>()<transacts>:int = 1 | 11
two := class(abs):
    Get<override>()<transacts>:int = 2
Main()<transacts>:void =
    Ss : []shape = array{shape{K := 1}, square{K := 2}, big{K := 3}, circle{K := 4}}
    for (S : Ss, X := S.Sizes()):
        Print("{X}")
    Q : square = big{K := 5}
    for (X := Q.Sizes()):
        Print("q {X}")
    B := base{K := 5}
    S := sub{K := 7}
    for (X := B.Vals()):
        Print("b {X}")
    for (X := S.Vals()):
        Print("s {X} {S.N}")
    for (X := S.Twice()):
        Print("t {X}")
    if (X := S.Vals(), X < 0):
        Print("neg {X}")
    if (X := S.Vals(), X > 1000):
        Print("never")
    Print("n {S.N}")
    As : []abs = array{one{}, two{}}
    for (A : As, X := A.Get()):
        Print("g {X}")
