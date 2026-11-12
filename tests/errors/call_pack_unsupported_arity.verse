# expect: no overload of F fits a call with 3 positional argument(s)
F(X:int):int=X
F(X:float):int=0
Main():void=Print("{F(1,2,3)}")
