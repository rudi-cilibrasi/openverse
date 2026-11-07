# expect: F is defined twice with parameters a call cannot tell apart, (t) and (int)
F(X:t where t:type):int = 0
F(X:int):int = 1
Main():void = Print("x")
