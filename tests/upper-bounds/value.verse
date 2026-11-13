vehicle:=class<computes>:
    Speed:int=1
    ReadSpeed()<computes>:int=Speed
car:=class<computes>(vehicle){Name:string="precise"}
truck:=class<computes>(vehicle){}
Identity(X:t where t:subtype(vehicle))<computes>:t=X
Read(X:t where t:subtype(vehicle))<computes>:int=X.Speed
Main():void=
    F:type{_(:car)<computes>:car}=Identity
    G:type{_(:car)<computes>:int}=Read
    C:=car{Speed:=9}
    Print("value {F(C).Name} {G(C)}")
