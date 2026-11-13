vehicle:=class<computes>{N:int=1}
car:=class<computes>(vehicle){}
reader:=class<computes>:
    Read(X:vehicle)<computes>:vehicle=X
Build(X:t where t:subtype(vehicle))<computes>:type{_(:t)<computes>:vehicle}=
    F:type{_(:vehicle)<computes>:vehicle}=reader{}.Read
    F
Main():void={}
