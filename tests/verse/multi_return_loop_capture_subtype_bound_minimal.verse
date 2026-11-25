Vehicle:=class<computes>{N:int=1}
Pick(X:t where t:subtype(Vehicle))<transacts>:int=
    var Steps:int=0
    for(V:=(3|X.N)):
        set Steps+=1
        if(V=1):return V|V+1000
    7
Main()<transacts>:void=
    for(V:=Pick(Vehicle{})):Print("all {V}")
