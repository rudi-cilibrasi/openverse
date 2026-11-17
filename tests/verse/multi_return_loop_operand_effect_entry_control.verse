cell:=class{var N:int=0}
Mark(H:cell,I:int)<transacts>:void=
    set H.N+=10
    Print("pre {I} {H.N}")
F(H:cell,N:int)<transacts>:int=
    defer:
        set H.N+=100
        Print("out {H.N}")
    if(N>=1):Mark(H,1)
    if(N>=2):
        Mark(H,2)
        return H.N|H.N+1
    H.N|H.N+1
Main()<transacts>:void=
    A:=cell{}
    for(V:=F(A,3)){Print("all {V}")}
    Print("state {A.N}")
    B:=cell{}
    if(V:=F(B,3),V=21)then Print("first {V}")else Print("bad")
    Print("state {B.N}")
    C:=cell{}
    if(V:=F(C,3),V=999)then Print("bad")else Print("none {C.N}")
    D:=cell{}
    for(V:=F(D,1)){Print("short {V}")}
    E:=cell{}
    for(V:=F(E,0)){Print("empty {V}")}
    Print("after")
