Reader:=class{N:int}
Read(R:Reader,N:int)<computes>:int=if(N>0)then Read(R,N-1)else R.N
One()<computes>:int=11
Caller(R:Reader,F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:int=
    var Stored:type{_()<computes>:int}=F
    for(I:=1..N):
        set Stored=Dummy
        Saved:=Stored
        if(I=2):return Read(R,N)|Read(R,N)+1
    F()|F()
Wrap(R:Reader,N:int)<computes>:[]int=for(V:=Caller(R,One,One,N)){V}
Main():void=for(V:Wrap(Reader{N:=7},3)){Print("v {V}")}
