# expect: expected type{_(:int):int}, found type{_(:int)<suspends>:int}
S(X:int)<suspends>:int = X
Main():void =
    F:int->int = S
    Print("{F(1)}")
