# expect: generic functions cannot be overloaded yet (F)
F(X:t where t:type):t = X
F(S:string):string = S
Main():void = Print("x")
