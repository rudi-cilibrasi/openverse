vehicle:=class<computes>{N:int=7}
car:=class<computes>(vehicle){}
slot(v:subtype(vehicle)):=interface<computes>:
    Take(X:t where t:subtype(vehicle))<computes>:t
impl(v:subtype(vehicle)):=class<computes>(slot(v)):
    (slot:)Take<override>(X:u where u:subtype(car))<computes>:u=X
Main():void={}
