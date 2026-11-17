cell:=class{var N:int=0}
Tick(H:cell)<transacts>:int=
    set H.N+=1
    Print("tick {H.N}")
    10
F(H:cell,N:int,?Bias:int=Tick(H))<transacts>:int=
    for(I:=1..N):
        if(I=2):return Bias+I|Bias+I+1
    Bias|Bias+1
Main()<transacts>:void=
    H:=cell{}
    for(V:=F(H,3)){Print("value {V}")}
    Print("state {H.N}")
    J:=cell{}
    if(V:=F(J,3),V=13)then Print("first {V}")else Print("bad")
    Print("state {J.N}")
    K:=cell{}
    if(V:=F(K,3),V=99)then Print("bad")else Print("none {K.N}")
    L:=cell{}
    for(V:=F(L,3,?Bias:=20)){Print("explicit {V}")}
    Print("state {L.N}")
    Print("after")
