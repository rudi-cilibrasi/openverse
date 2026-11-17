# Ordinary scalar producer; only the caller chooses the fallthrough value.
cell:=class{var N:int=0}
F(H:cell,X:int,Next:logic)<transacts>:int=
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
    if(Next?)then H.N+1 else H.N
Main()<transacts>:void=
    A:=cell{}
    if(Next:=false|true,V:=F(A,3,Next),V=13)then Print("found {V} {A.N}")else Print("bad")
    B:=cell{}
    if(Next:=false|true,V:=F(B,3,Next),V=14)then Print("bad")else Print("none {B.N}")
    C:=cell{}
    if(Next:=false|true,V:=F(C,1,Next),V=1012)then Print("second {V} {C.N}")else Print("bad")
    Print("after")
