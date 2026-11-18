Cell:=class{var N:int=0}
Seed(S:Cell)<transacts>:int=
    set S.N+=1
    Print("seed {S.N}")
    0
Pick(S:Cell,Limit:int)<transacts>:int=
    for(var N:int=Seed(S), Limit>0, A:=block{W:=1|2; W}|3, A<=Limit, var Row:int=A*100+N):
        set N+=1
        set Row+=1
        Y:=N|N+10
        defer:Print("cleanup {A} {Y} {N} {Row}")
        if(A=2):return Row+Y
        Print("advance {A} {Y}")
    S.N+900
Main()<transacts>:void=
    S:=Cell{}
    for(V:=Pick(S,2)):Print("all {V}")
    Print("state {S.N}")
    First:=Cell{}
    if(V:=Pick(First,2),V=214)then Print("first {V}")else Print("missed")
    Print("state {First.N}")
    UseFallback:=Cell{}
    for(V:=Pick(UseFallback,1)):Print("fallback {V}")
    Print("state {UseFallback.N}")
    Reject:=Cell{}
    if(V:=Pick(Reject,2),V=9999)then Print("bad")else Print("reject {Reject.N}")
    Empty:=Cell{}
    for(V:=Pick(Empty,0)):Print("empty {V}")
    Print("state {Empty.N}")
