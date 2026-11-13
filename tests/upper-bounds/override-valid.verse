vehicle:=class<computes>:
    Speed:int=1
    ReadSpeed()<computes>:int=Speed
car:=class<computes>(vehicle){Name:string="precise"}
truck:=class<computes>(vehicle){}
base:=interface<computes>:
    F(X:t where t:subtype(vehicle))<computes>:t
impl:=class<computes>(base):
    F<override>(X:u where u:subtype(vehicle))<computes>:u=X
Main():void=
    I:base=impl{}
    Print("override {I.F(car{}).Name}")
