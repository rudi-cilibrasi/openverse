# expect: X has a default but is not named: only a named parameter has one
F(X:int = 0):int = X
Main():void = Print("{F(1)}")
