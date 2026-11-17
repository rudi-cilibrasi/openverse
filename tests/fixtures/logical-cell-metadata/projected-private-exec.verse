Inner:=class{Work:type{_()<computes>:int}}
Outer:=class{Box:Inner}
One()<computes>:int=11
Caller(H:Outer,F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<transacts>:type{_()<computes>:int}=
    var Stored:type{_()<computes>:int}=Dummy
    for(I:=1..N):
        set Stored=Dummy
        X:=Stored()
        if(I=2):return Stored|Stored
    F|F
Wrap(H:Outer,F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<transacts>:void=
    for(G:=Caller(H,F,Dummy,N)):
        Print("row")
Main()<transacts>:void=Wrap(Outer{Box:=Inner{Work:=One}},One,One,3)
