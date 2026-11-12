# expect: expected int, found tuple(string, string)
NeedsInt(X:int):int = X
F(X:int,Y:int):int = X+Y
F(X:string):int = 0
Main():void = Print("{F((NeedsInt(("bad","pair")),2))}")
