# expect: 'F' is defined twice (only functions can be overloaded)
F:int = 3
F(S:string):int = 0
F(X:int):int = 1
Main():void = Print("x")
