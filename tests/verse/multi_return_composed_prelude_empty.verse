Cell:=class{var N:int=0}
Prelude(S:Cell)<transacts>:int=
    set S.N+=1
    50
Pick(S:Cell,Permit:int)<transacts>:int=
    for(P:=Prelude(S), Permit>0, A:=block{W:=1|2;W}|3,A=99):
        Y:=A|P
        if(A>0):return Y
    S.N|S.N+10
Main()<transacts>:void=
    S:=Cell{}
    for(V:=Pick(S,1)):Print("empty {V}")
    Print("state {S.N}")
    T:=Cell{}
    for(V:=Pick(T,0)):Print("failed {V}")
    Print("state {T.N}")
