# expect: parameters a call cannot tell apart
F(P:tuple()):int=1
F():int=2
Main():void=Print("{F()}")
