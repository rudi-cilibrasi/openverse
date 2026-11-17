Caller(F:t,Dummy:t,N:int where t:type)<computes>:t=
    var Stored:t=F
    for(I:=1..N):
        set Stored=Dummy
        if(I=1):return Stored|Stored
    F|F
Main():void={}
