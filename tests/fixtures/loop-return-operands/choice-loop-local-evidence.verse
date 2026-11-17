vehicle:=class<computes>{N:int=7}
Low()<computes>:int=1|2
F(X:t,D:?evidence(vehicle,t) where t:type)<computes>:int=
    if(P:=D?):
        for(I:=Low()..X.N):
            if(I=X.N):return X.N|X.N+1
    0|1
Main():void={}
