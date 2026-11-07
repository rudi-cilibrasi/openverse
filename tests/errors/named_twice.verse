# expect: ?N is given twice
F(X:int, ?N:int = 0):int = X + N
Main():void = Print("{F(1, ?N := 1, ?N := 2)}")
