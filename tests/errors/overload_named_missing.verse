# expect: no overload of F fits a call with 1 positional argument(s); its overloads take (int, ?N:int) and (int, ?M:int)
F(X:int, ?N:int):int = 0
F(X:int, ?M:int):int = 1
Main():void = Print("{F(1)}")
