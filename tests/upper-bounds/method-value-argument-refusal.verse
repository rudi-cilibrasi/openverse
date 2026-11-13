vehicle:=class<computes>{N:int=1}
car:=class<computes>(vehicle){}
reader:=class<computes>:
    Read(X:car)<computes>:vehicle=X
Build(X:t where t:subtype(vehicle))<computes>:type{_(:t)<computes>:vehicle}=reader{}.Read
Main():void={}
