Inner:=class{Work:type{_()<computes>:int}}
Outer:=class{Box:Inner}
One()<computes>:int=11
Caller(H:Outer,Dummy:Outer,N:int)<transacts>:Outer=
    var Stored:Outer=Dummy
    for(I:=1..N):
        set Stored=Dummy
        X:=Stored.Box.Work()
        if(I=2):return Stored|Stored
    H|H
Wrap(H:Outer,Dummy:Outer,N:int)<transacts>:void=
    for(G:=Caller(H,Dummy,N)){Print("row")}
Main()<transacts>:void=Wrap(Outer{Box:=Inner{Work:=One}},Outer{Box:=Inner{Work:=One}},3)
