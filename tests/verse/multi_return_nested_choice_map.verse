State:=class{var N:int=0}
Bounds()<computes>:int=1|2
Sources(I:int)<computes>:[string]int=map{}|map{"a"=>I,"b"=>I+10}
OuterEnd(S:State,I:int)<transacts>:void=
    set S.N+=100
    Print("outer {I} {S.N}")
InnerEnd(S:State,Key:string)<transacts>:void=
    set S.N+=10
    Print("inner {Key} {S.N}")
Pick(S:State,Need:int)<transacts>:int=
    for(Outer:=Bounds()..2):

        defer:OuterEnd(S,Outer)
        for(K -> V:Sources(Outer)):
            set S.N+=V
            defer:InnerEnd(S,K)
            if(V=Need):return S.N|block{Print("second {S.N}");S.N+1000}
    S.N|S.N+2000
Main()<transacts>:void=
    A:=State{}
    for(V:=Pick(A,12)):Print("all {V}")
    Print("state {A.N}")
    B:=State{}
    if(V:=Pick(B,12),V>1000)then Print("first {V}")else Print("missing")
    Print("state {B.N}")
    C:=State{}
    if(V:=Pick(C,12),V=9999)then Print("bad")else Print("none {C.N}")
    D:=State{}
    for(V:=Pick(D,99)):Print("suffix {V}")
    Print("state {D.N}")
