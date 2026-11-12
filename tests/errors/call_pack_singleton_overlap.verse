# expect: parameters a call cannot tell apart
F(P:tuple(int)):int=1
F(A:int):int=2
Main():void=Print("{F(1)}")
