# expect: no overload of F takes 3 argument(s)
F(X:int):int = X
F(S:string):int = 0
Main():void = Print("{F(1, 2, 3)}")
