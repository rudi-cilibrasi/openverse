# expect: parameters a call cannot tell apart
F(P:t where t:type):int=1
F(A:int,B:string):int=2
Main():void=Print("{F(1,"x")}")
