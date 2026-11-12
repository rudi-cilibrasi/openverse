# expect: call cannot tell apart
F(X:tuple(t),Y:t where t:type):int = 1
F(X:[]int,Y:t where t:type):int = 2
Main():void = {}
