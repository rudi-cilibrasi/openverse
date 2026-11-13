vehicle:=class<computes>{}
car:=class<computes>(vehicle){}
splitter(v:subtype(vehicle)):=class<computes>:
    Item:v
    Split(X:u where t:type,u:subtype(t))<computes>:u=X
Bind(H:splitter(v) where v:subtype(vehicle))<computes>:type{_(:int,:string)<computes>:tuple(int,string)}=H.Split
Main():void=
    H:=splitter(car){Item:=car{}}
    M:=Bind(H)
    R:=M(5,"m")
    Print("tuple method {R(0)} {R(1)}")
