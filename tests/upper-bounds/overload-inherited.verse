vehicle:=class<computes>{}
car:=class<computes>(vehicle){}
truck:=class<computes>(vehicle){}
base(a:subtype(vehicle)):=class<computes>:
    Select(X:a)<computes>:int=5
narrow(u:subtype(car)):=class<computes>(base(u)):
    Select(X:t where t:subtype(truck))<computes>:int=6
Main():void=
    R:=narrow(car){}
    Print("inherited {R.Select(car{})} {R.Select(truck{})}")
