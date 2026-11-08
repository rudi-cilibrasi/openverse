# expect: a value of type type{_(:int):int} takes 1 argument(s), found 2
D(X:int):int = X
Main():void =
    F:int->int = D
    Print("{F(1, 2)}")
