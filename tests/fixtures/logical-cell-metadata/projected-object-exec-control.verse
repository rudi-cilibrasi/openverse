Inner:=class{Work:type{_()<computes>:int}}
Outer:=class{Box:Inner}
One()<computes>:int=11
Caller(H:Outer,Dummy:Outer,N:int)<transacts>:Outer=
    var Stored:Outer=Dummy
    if(N>=1):
        set Stored=Dummy
        X1:=Stored.Box.Work()
    if(N>=2):
        set Stored=Dummy
        X2:=Stored.Box.Work()
        return Stored|Stored
    H|H
Wrap(H:Outer,Dummy:Outer,N:int)<transacts>:void=
    for(G:=Caller(H,Dummy,N)){Print("row")}
Main()<transacts>:void=Wrap(Outer{Box:=Inner{Work:=One}},Outer{Box:=Inner{Work:=One}},3)
