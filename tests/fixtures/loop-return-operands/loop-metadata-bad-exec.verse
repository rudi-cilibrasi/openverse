One()<computes>:int=11
Two()<computes>:int=22
Produce(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:type{_()<computes>:int}=
    var Stored:type{_()<computes>:int}=F
    set Stored=Dummy
    for(I:=1..N):
        if(I=2):return Stored|Stored
    Dummy|Dummy
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    Rows:=for(G:=Produce(F,Dummy,3)):
        Print("got {G()}")
        1
    Rows.Length
Main():void=Print("count {Caller(One,Two)}")
