cell:=class{var N:int=0}
F(H:cell,X:int)<transacts>:int=
    defer:
        set H.N+=100
        Print("out {H.N}")
    for(I:=1..X):
        defer:
            set H.N+=10
            Print("iter {I} {H.N}")
        set H.N+=I
        if(I=2):return H.N
    set H.N+=1000
    H.N|H.N+1
Main()<transacts>:void=
    A:=cell{}
    if(V:=F(A,3),V=13)then Print("found {V} {A.N}")else Print("bad")
    B:=cell{}
    if(V:=F(B,3),V=14)then Print("bad")else Print("none {B.N}")
    C:=cell{}
    if(V:=F(C,1),V=1012)then Print("second {V} {C.N}")else Print("bad")
    Print("after")
