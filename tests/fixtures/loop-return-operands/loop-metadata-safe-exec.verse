One()<computes>:int=11
Two()<computes>:int=22
Produce(F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:type{_()<computes>:int}=
    var Stored:type{_()<computes>:int}=Dummy
    set Stored=F
    for(I:=1..N):
        if(I=2):return Stored|Stored
    F|F
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    Rows:=for(G:=Produce(F,Dummy,3)):
        Print("got {G()}")
        1
    Rows.Length
Main():void=Print("count {Caller(One,Two)}")
