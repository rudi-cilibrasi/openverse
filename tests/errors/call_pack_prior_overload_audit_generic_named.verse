# expect: parameters a call cannot tell apart
F(X:t,?N:int=7 where t:type)<computes>:int=N
F(X:int,Y:int)<computes>:int=X+Y
Main():void=Print("{F("s")} {F(1,2)} {F("s",?N:=9)}")
