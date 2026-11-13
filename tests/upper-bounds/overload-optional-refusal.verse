vehicle:=class<computes>{}
car:=class<computes>(vehicle){}
truck:=class<computes>(vehicle){}
F(?X:t=car{} where t:subtype(car))<computes>:int=1
F(?X:t=truck{} where t:subtype(truck))<computes>:int=2
Main():void={}
