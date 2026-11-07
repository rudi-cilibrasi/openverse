# expect: C is defined twice with parameters a call cannot tell apart, (int, ?N:int) and (int)
C(X:int, ?N:int = 0):int = 0
C(X:int):int = 1
Main():void = Print("x")
