Reader:=class{N:int}
Read(R:Reader,N:int)<computes>:int=if(N>0)then Read(R,N-1)else R.N
One()<computes>:int=11
Caller(R:Reader,F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<computes>:int=
    var Stored:type{_()<computes>:int}=F
    if(N>=1):
        set Stored=Dummy
        Saved1:=Stored
    if(N>=2):
        set Stored=Dummy
        Saved2:=Stored
        return Read(R,N)|Read(R,N)+1
    F()|F()
Wrap(R:Reader,N:int)<computes>:[]int=for(V:=Caller(R,One,One,N)){V}
Main():void=for(V:Wrap(Reader{N:=7},3)){Print("v {V}")}
