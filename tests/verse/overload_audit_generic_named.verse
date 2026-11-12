F(X:t,?Tag:logic,?N:int=7 where t:type)<computes>:int=N
F(X:int,Y:int)<computes>:int=X+Y
Main():void=Print("{F("s",?Tag:=true)} {F(1,2)} {F("s",?N:=9,?Tag:=true)}")
