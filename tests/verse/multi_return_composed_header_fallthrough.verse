Cell:=class{var N:int=0}
Prelude(S:Cell)<transacts>:int=
    set S.N+=1000
    S.N
Source(S:Cell,A:int,X:int)<transacts>:[]int=
    set S.N+=1
    if(A=3)then array{} else array{X+10,X+11}
Cleanup(S:Cell,B:int,Y:int)<transacts>:void=
    set S.N+=1
    Print("cleanup {B} {Y} {S.N}")
Pick(S:Cell)<transacts>:int=
    for(A:=block{Prelude(S); W:=1|2; W}|3, X:=A*100, B:Source(S,A,X)):
        Y:=B|B+1000
        defer:Cleanup(S,B,Y)
        if(B>=210 or Y=110):
            return Y|Y+10000
        Print("advance {B} {Y}")
    S.N
Main()<transacts>:void=
    S:=Cell{}
    for(V:=Pick(S)):Print("all {V}")
    Print("state {S.N}")
    First:=Cell{}
    if(V:=Pick(First),V=110)then Print("first {V}")else Print("missed")
    Print("state {First.N}")
    Later:=Cell{}
    if(V:=Pick(Later),V=1210)then Print("later {V}")else Print("missed")
    Print("state {Later.N}")
    Reject:=Cell{}
    if(V:=Pick(Reject),V=9999)then Print("bad")else Print("reject {Reject.N}")
