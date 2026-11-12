vehicle:=class<computes>:
    Speed:int=1
    ReadSpeed()<computes>:int=Speed
car:=class<computes>(vehicle){Name:string="precise"}
truck:=class<computes>(vehicle){}
base(t:subtype(vehicle)):=interface<computes>:
    Read()<computes>:t
child(u:subtype(car)):=class<computes>(base(u)):
    Value:u
    Read<override>()<computes>:u=Value
Main():void=
    I:base(car)=child(car){Value:=car{}}
    Print("receiver override {I.Read().Name}")
