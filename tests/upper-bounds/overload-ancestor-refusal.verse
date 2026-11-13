vehicle:=class<computes>{}
car:=class<computes>(vehicle){}
F(X:t where t:subtype(vehicle))<computes>:int=1
F(X:t where t:subtype(car))<computes>:int=2
Main():void={}
