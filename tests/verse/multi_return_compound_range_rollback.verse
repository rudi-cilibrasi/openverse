State:=class{var N:int=0}
Low(S:State)<transacts>:int=
    set S.N+=1
    1|2
High(S:State,Limit:int)<transacts>:int=
    set S.N+=10
    Limit
Inner(S:State,I:int,Enabled:logic)<transacts><decides>:int=
    set S.N+=100
    Enabled?
    I=2
    1
Pick(S:State,Enabled:logic,Limit:int)<transacts>:int=
    for(I:=Low(S)..High(S,Limit),J:=Inner[S,I,Enabled]..1):
        if(I=2,J=1):return S.N|S.N+1
    S.N|S.N+1000
Main()<transacts>:void=
    A:=State{}
    for(V:=Pick(A,true,9223372036854775807)):Print("all {V}")
    Print("committed {A.N}")
    B:=State{}
    for(V:=Pick(B,false,3)):Print("empty {V}")
    Print("rolled back {B.N}")
