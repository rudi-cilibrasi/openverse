vehicle:=class<computes>{N:int=1}
car:=class<computes>(vehicle){}
reader:=class<computes>:
    Read(X:vehicle)<computes>:vehicle=X
Build(X:car)<computes>:type{_(:car)<computes>:vehicle}=
    F:type{_(:vehicle)<computes>:vehicle}=reader{}.Read
    F
Main():void={}
