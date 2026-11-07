# expect: no overload of F takes (logic)
F(X:int):int = X
F(S:string):int = 0
Main():void = Print("{F(true)}")
