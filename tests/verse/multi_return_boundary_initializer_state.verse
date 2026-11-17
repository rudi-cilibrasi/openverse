cell:=class{var N:int=0}
F(H:cell,X:int)<transacts>:int=
    defer:
        set H.N+=100
        Print("out {H.N}")
    Y:=block:
        defer:
            set H.N+=10
            Print("init {H.N}")
        set H.N+=X
        if(X=2):return H.N
        H.N
    defer:Print("late")
    Y|Y+1
Main()<transacts>:void=
    A:=cell{}
    if(V:=F(A,2),V=2)then Print("found {V} {A.N}")else Print("bad")
    B:=cell{}
    if(V:=F(B,2),V=3)then Print("bad")else Print("none {B.N}")
    C:=cell{}
    if(V:=F(C,1),V=2)then Print("normal {V} {C.N}")else Print("bad")
    Print("after")
