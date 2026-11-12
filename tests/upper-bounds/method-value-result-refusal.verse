vehicle:=class<computes>{N:int=1}
car:=class<computes>(vehicle){}
reader:=class<computes>:
    Get()<computes>:vehicle=vehicle{}
Build(X:t where t:subtype(vehicle))<computes>:type{_()<computes>:t}=reader{}.Get
Main():void={}
