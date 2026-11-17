cell:=class{var N:int=0}
Low(H:cell,N:int)<transacts><decides>:int=
    set H.N+=1
    Print("low {H.N}")
    N>=0
    1
High(H:cell,N:int)<transacts><decides>:int=
    if(N<0):Err()
    set H.N+=1
    Print("high {H.N}")
    N>0
    2
F(H:cell,N:int)<transacts>:int=
    defer:
        set H.N+=10
        Print("out {H.N}")
    for(I:=Low[H,N]..High[H,N]):
        if(I=2):return I|I+1
    N|N+1
Main()<transacts>:void=
    A:=cell{}
    for(V:=F(A,3)){Print("yes {V}")}
    Print("state {A.N}")
    B:=cell{}
    for(V:=F(B,0)){Print("upper {V}")}
    Print("state {B.N}")
    C:=cell{}
    for(V:=F(C,-1)){Print("lower {V}")}
    Print("state {C.N}")
    D:=cell{}
    if(V:=F(D,3),V=3)then Print("first {V}")else Print("bad")
    Print("state {D.N}")
    E:=cell{}
    if(V:=F(E,0),V=1)then Print("fallback {V}")else Print("bad")
    Print("state {E.N}")
    G:=cell{}
    if(V:=F(G,3),V=999)then Print("bad")else Print("none {G.N}")
    Print("after")
