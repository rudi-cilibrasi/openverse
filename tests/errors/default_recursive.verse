# expect: the default of ?Y of F uses itself
F(X:int, ?Y:int = if (X > 0) then F(X - 1) else 0):int = X + Y
Main():void = Print("{F(3)}")
