# expect: 3:4: a.Vals has several values, but Vals is overloaded: such methods are not supported yet
a := class:
    Vals()<transacts>:int = 1 | 2
    Vals(X : int)<transacts>:int = X
Main()<transacts>:void =
    for (X := a{}.Vals()):
        Print("{X}")
