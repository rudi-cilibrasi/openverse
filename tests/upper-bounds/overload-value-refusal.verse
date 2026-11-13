vehicle:=class<computes>{}
car:=class<computes>(vehicle){}
truck:=class<computes>(vehicle){}
F(X:t where t:subtype(car))<computes>:int=1
F(X:t where t:subtype(truck))<computes>:int=2
Main():void=
    V:type{_(:car)<computes>:int}=F
    Print("{V(car{})}")
