vehicle:=class<computes>{}
car:=class<computes>(vehicle){}
truck:=class<computes>(vehicle){}
base(a:subtype(vehicle)):=class<computes>:
    Select(X:t where t:subtype(car))<computes>:int=1
narrow(t:subtype(truck)):=class<computes>(base(t)):
    Select(X:car)<computes>:int=2
Main():void={}
