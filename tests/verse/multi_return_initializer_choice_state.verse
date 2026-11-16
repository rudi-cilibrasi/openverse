cell:=class{var N:int=0}
F(H:cell,X:int)<transacts>:int=
    defer:
        set H.N+=100
        Print("out {H.N}")
    Y:=if(X>2)then(return 0)else block:
        defer:
            set H.N+=10
            Print("init {H.N}")
        set H.N+=1
        H.N|H.N+1
    defer:Print("late {H.N}")
    Y|Y+1
Main()<transacts>:void=
    A:=cell{}
    for(V:=F(A,1)){Print("all {V} {A.N}")}
    B:=cell{}
    if(V:=F(B,1),V=2)then Print("first {V} {B.N}")else Print("bad")
    C:=cell{}
    if(V:=F(C,1),V=3)then Print("last {V} {C.N}")else Print("bad")
    D:=cell{}
    if(V:=F(D,1),V=99)then Print("bad")else Print("none {D.N}")
    E:=cell{}
    for(V:=F(E,3)){Print("early {V} {E.N}")}
    Print("after")
