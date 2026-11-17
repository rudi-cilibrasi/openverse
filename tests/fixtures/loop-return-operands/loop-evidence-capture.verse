vehicle:=class<computes>{N:int=7}
F(X:t,D:evidence(vehicle,t),N:int where t:type)<computes>:int=
    for(I:=1..N):
        if(I=2):return X.N|X.N+1
    X.N|X.N+1
Main():void={}
