vehicle:=class<computes>:
    Speed:int=1
    ReadSpeed()<computes>:int=Speed
car:=class<computes>(vehicle){Name:string="precise"}
truck:=class<computes>(vehicle){}
base:=interface<computes>:
    F(X:t where t:subtype(vehicle))<computes>:t
impl:=class<computes>(base):
    F<override>(X:t where t:subtype(car))<computes>:t=X
Main():void={}
