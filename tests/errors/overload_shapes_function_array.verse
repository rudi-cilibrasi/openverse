# expect: call cannot tell apart
F(X:[]int):int = 1
F(X:type{_(:string)<computes>:int}):int = 2
Main():void = {}
