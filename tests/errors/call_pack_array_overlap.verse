# expect: parameters a call cannot tell apart
F(P:[]int):int=1
F(A:int,B:int):int=2
Main():void=Print("{F(1,2)}")
