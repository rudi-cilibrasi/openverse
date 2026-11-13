vehicle:=class<computes>:
    Speed:int=1
    ReadSpeed()<computes>:int=Speed
car:=class<computes>(vehicle){Name:string="precise"}
truck:=class<computes>(vehicle){}
F(?X:t=car{} where t:subtype(vehicle))<computes>:int=1|2
Main():void=for(V:=F()){Print("default {V}")}
