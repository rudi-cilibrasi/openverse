vehicle:=class<computes>{N:int=7}
car:=class<computes>(vehicle){}
F(X:t,U:u,N:int where u:subtype(vehicle),t:subtype(u))<computes>:int=
    for(I:=1..N):
        if(I=2):return X.N|X.N+1
    X.N|X.N+1
Main():void=
    for(V:=F(car{},vehicle{},3)){Print("value {V}")}
    if(V:=F(car{},vehicle{},3),V=8)then Print("first {V}")else Print("bad")
    Print("after")
