# expect: 9:12: a.Vals has several values, so it cannot be used as a function value
a := class:
    Vals()<transacts>:int = 1 | 2
b := class:
    Vals()<transacts>:int = 7
Main()<transacts>:void =
    G := b{}.Vals
    Print("{G()}")
    F := a{}.Vals
    Print("x")
