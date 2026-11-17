Cell:=class{var N:int=0}
Sources(S:Cell)<transacts>:[string]int=
    set S.N+=1
    map{}|map{"a"=>3,"b"=>4}|map{"later"=>9}
OuterCleanup(S:Cell,K:string)<transacts>:void=
    set S.N+=10
    Print("outer {K} {S.N}")
InnerCleanup(S:Cell,V:int)<transacts>:void=
    set S.N+=1
    Print("inner {V} {S.N}")
Pick(S:Cell,Need:int)<transacts>:int=
    for(K -> V:Sources(S)):
        set S.N+=V
        if(V=Need):
            defer:OuterCleanup(S,K)
            Y:=S.N|block{Print("second {S.N}");S.N+100}
            defer:InnerCleanup(S,Y)
            return Y|Y+1000
    S.N|S.N+1000
Main()<transacts>:void=
    A:=Cell{}
    for(V:=Pick(A,4)):Print("all {V}")
    Print("state {A.N}")
    B:=Cell{}
    if(V:=Pick(B,4),V=108)then Print("first {V}")else Print("none")
    Print("state {B.N}")
    C:=Cell{}
    if(V:=Pick(C,4),V=9999)then Print("bad")else Print("rejected {C.N}")
    D:=Cell{}
    for(V:=Pick(D,999)):Print("fallback {V}")
    Print("state {D.N}")
