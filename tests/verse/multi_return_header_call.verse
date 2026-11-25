Cell:=class{var N:int=0}
Choose(S:Cell,Pass:logic)<transacts><decides>:void=
    set S.N+=1000
    Pass?
Step(S:Cell,N:int)<transacts>:int=
    set S.N+=1
    N|N+1
Cleanup(S:Cell,V:int,Y:int)<transacts>:void=
    set S.N+=10
    Print("cleanup {V} {Y} {S.N}")
Composed(S:Cell,N:int)<transacts>:int=
    for(V:=3|Step(S,N)):
        Y:=V|V+100
        defer:Cleanup(S,V,Y)
        if(V=1):return Y|Y+1000
        Print("advance {V} {Y} {S.N}")
    S.N
Exclusive(S:Cell,Pass:logic,N:int)<transacts>:int=
    for(V:=if(Choose[S,Pass], N>=0)then (3|(if(N>0)then Step(S,N-1) else 1)) else (4|Step(S,N))):
        Y:=V|V+100
        defer:Cleanup(S,V,Y)
        if(V=1):return Y|Y+1000
        Print("advance {V} {Y} {S.N}")
    S.N
Main()<transacts>:void=
    A:=Cell{}
    for(V:=Composed(A,0)):Print("composed {V}")
    Print("state {A.N}")
    B:=Cell{}
    for(V:=Exclusive(B,true,1)):Print("then {V}")
    Print("state {B.N}")
    C:=Cell{}
    for(V:=Exclusive(C,false,0)):Print("else {V}")
    Print("state {C.N}")
    F:=Cell{}
    if(V:=Exclusive(F,true,1),V=101)then Print("first {V}")else Print("missed")
    Print("state {F.N}")
    R:=Cell{}
    if(V:=Exclusive(R,false,0),V=9999)then Print("bad")else Print("reject {R.N}")
