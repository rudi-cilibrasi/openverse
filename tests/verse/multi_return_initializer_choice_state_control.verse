cell:=class{var N:int=0}
F(H:cell,X:int,Init:logic,Tail:logic)<transacts>:int=
    defer:
        set H.N+=100
        Print("out {H.N}")
    Y:=if(X>2)then(return 0)else block:
        defer:
            set H.N+=10
            Print("init {H.N}")
        set H.N+=1
        if(Init?)then H.N else H.N+1
    defer:Print("late {H.N}")
    if(Tail?)then Y else Y+1
Emit(H:cell,V:int)<transacts>:void=
    Print("late {H.N}")
    set H.N+=100
    Print("out {H.N}")
    Print("all {V} {H.N}")
Main()<transacts>:void=
    A:=cell{}
    set A.N+=1
    Y:=A.N
    set A.N+=10
    Print("init {A.N}")
    Emit(A,Y)
    Emit(A,Y+1)
    Z:=A.N+1
    set A.N+=10
    Print("init {A.N}")
    Emit(A,Z)
    Emit(A,Z+1)
    B:=cell{}
    if(Init:=true|false,Tail:=true|false,V:=F(B,1,Init,Tail),V=2)then Print("first {V} {B.N}")else Print("bad")
    C:=cell{}
    if(Init:=true|false,Tail:=true|false,V:=F(C,1,Init,Tail),V=3)then Print("last {V} {C.N}")else Print("bad")
    D:=cell{}
    if(Init:=true|false,Tail:=true|false,V:=F(D,1,Init,Tail),V=99)then Print("bad")else Print("none {D.N}")
    E:=cell{}
    V:=F(E,3,true,true)
    Print("early {V} {E.N}")
    Print("after")
