vehicle:=class<computes>:
    Speed:int=1
    ReadSpeed()<computes>:int=Speed
car:=class<computes>(vehicle){Name:string="precise"}
truck:=class<computes>(vehicle){}
pair(a:type,b:type):=class<computes>{A:a;B:b}
dup(v:subtype(vehicle)):=class<computes>(pair(v,v)){}
F(P:pair(a,b) where a:type,b:type)<computes>:int=if(Q:=dup[P])then Q.A.Speed else 0
Main():void=Print("refined {F(dup(car){A:=car{Speed:=9},B:=car{}})}")
