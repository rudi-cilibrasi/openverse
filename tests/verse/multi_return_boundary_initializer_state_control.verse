# Ordinary scalar producer; only the caller chooses the fallthrough value.
cell:=class{var N:int=0}
F(H:cell,X:int,Next:logic)<transacts>:int=
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
    if(Next?)then Y+1 else Y
Main()<transacts>:void=
    A:=cell{}
    if(Next:=false|true,V:=F(A,2,Next),V=2)then Print("found {V} {A.N}")else Print("bad")
    B:=cell{}
    if(Next:=false|true,V:=F(B,2,Next),V=3)then Print("bad")else Print("none {B.N}")
    C:=cell{}
    if(Next:=false|true,V:=F(C,1,Next),V=2)then Print("normal {V} {C.N}")else Print("bad")
    Print("after")
