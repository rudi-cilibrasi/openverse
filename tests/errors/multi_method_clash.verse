# expect: 3:4: a.Vals has several values, but another class or interface ha
a := class:
    Vals()<transacts>:int = 1 | 2
b := class:
    Vals()<transacts>:int = 7
Main()<transacts>:void =
    for (X := a{}.Vals()):
        Print("{X}")
