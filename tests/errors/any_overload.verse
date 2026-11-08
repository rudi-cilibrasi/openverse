# expect: 3:0: F is defined twice with parameters a call cannot tell apart, (int) and (any): overloads must take disjoint types
F(X:int):int = 1
F(X:any):int = 2
Main():void = Print("x")
