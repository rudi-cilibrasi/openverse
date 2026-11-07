# expect: 'F' is defined twice (only functions can be overloaded)
F := class:
    X:int = 0
F(S:string):int = 0
F(X:int):int = 1
Main():void = Print("x")
