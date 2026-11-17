cell:=class{var N:int=0}
Low(H:cell)<transacts>:int=
    set H.N+=1
    Print("low {H.N}")
    1
High(H:cell)<transacts>:int=
    set H.N+=1
    Print("high {H.N}")
    3
F(H:cell)<transacts>:int=
    defer:
        set H.N+=10
        Print("out {H.N}")
    for(I:=Low(H)..High(H)):
        if(I=2):return H.N|H.N+1
    H.N|H.N+1
Main()<transacts>:void=
    A:=cell{}
    for(V:=F(A)){Print("all {V}")}
    Print("state {A.N}")
    B:=cell{}
    if(V:=F(B),V=3)then Print("first {V}")else Print("bad")
    Print("state {B.N}")
    C:=cell{}
    if(V:=F(C),V=99)then Print("bad")else Print("none {C.N}")
    Print("after")
