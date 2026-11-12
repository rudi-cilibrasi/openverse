# expect: call cannot tell apart
F(X:tuple(int),Y:int):int = 1
F(X:?int,Y:int):int = 2
Main():void = {}
