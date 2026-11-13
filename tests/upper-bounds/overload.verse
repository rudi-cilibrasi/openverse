vehicle:=class<computes>:
    Speed:int=1
    ReadSpeed()<computes>:int=Speed
car:=class<computes>(vehicle){Name:string="precise"}
truck:=class<computes>(vehicle){}
F(X:t where t:subtype(car))<computes>:int=1
F(X:t where t:subtype(truck))<computes>:int=2
Main():void=Print("overload {F(car{})} {F(truck{})}")
