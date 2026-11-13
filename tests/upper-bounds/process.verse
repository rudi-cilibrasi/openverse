vehicle:=class<computes>:
    Speed:int=1
    ReadSpeed()<computes>:int=Speed
car:=class<computes>(vehicle){Name:string="precise"}
truck:=class<computes>(vehicle){}
Process(X:t where t:subtype(vehicle))<computes>:t=
    Print("speed {X.Speed}")
    X
Main():void=Print("name {Process(car{Speed:=9}).Name}")
