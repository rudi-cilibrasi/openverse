# expect: needs the argument ?Y
F(X:int, ?Y:int):int = X + Y
Main():void =
    Print("{F(1)}")
