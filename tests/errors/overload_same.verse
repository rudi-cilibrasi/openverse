# expect: F is defined twice with parameters a call cannot tell apart, (int) and (int)
F(X:int):int = X
F(Y:int):int = Y
Main():void = Print("x")
