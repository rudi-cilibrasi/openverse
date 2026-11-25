Expr(t:type) := class<abstract>:
    Eval()<computes>:t
Lit := class(Expr(int)):
    V:int
    Eval<override>()<computes>:int=V
Pair(a:type,b:type) := class(Expr(tuple(a,b))):
    L:Expr(a)
    R:Expr(b)
    Eval<override>()<computes>:tuple(a,b)=(L.Eval(),R.Eval())
PlainPair:=class(Expr(tuple(int,int))):
    Eval<override>()<computes>:tuple(int,int)=(4,8)
Cell:=class<allocates>{var N:int=0}
Box:=class<computes>{K:int=5}
PickC(E:Expr(t) where t:type)<computes>:int=
    for(V:=if(P:=Pair[E], X:=Lit[P.L])then (X.V|1) else (4|1)):
        Y:=V|V+100
        if(V=1):return Y|Y+1000
    99
PickR(S:Cell,E:Expr(t) where t:type)<reads>:int=
    for(V:=if(P:=Pair[E], X:=Lit[P.L])then (X.V|1) else (4|1)):
        Y:=V|V+S.N
        if(V=1):return Y|Y+1000
    S.N
PickA(E:Expr(t) where t:type)<allocates>:int=
    for(V:=if(P:=Pair[E], X:=Lit[P.L])then (X.V|1) else (4|1)):
        B:=Cell{}
        Y:=V|V+200
        if(V=1):return Y|Y+1000
    98
PickT(S:Cell,E:Expr(t) where t:type)<transacts>:int=
    for(V:=if(P:=Pair[E], X:=Lit[P.L])then (X.V|1) else (4|1)):
        set S.N+=1
        Y:=V|V+S.N
        if(V=1):return Y|Y+1000
    S.N
PickTwice(S:Cell,E:Expr(t) where t:type)<transacts>:int=
    for(V:=if(P:=Pair[E], X:=Lit[P.L])then (X.V|1) else (4|1)):
        set S.N+=1
        if(V=7):return V|V+1000
    for(V:=if(P:=Pair[E], X:=Lit[P.L])then (X.V|1) else (4|1)):
        set S.N+=10
        Y:=V|V+S.N
        if(V=1):return Y|Y+1000
    S.N
Main()<transacts>:void=
    P:=Pair(int,int){L:=Lit{V:=3},R:=Lit{V:=7}}
    Q:=PlainPair{}
    S:=Cell{}
    set S.N=300
    for(V:=PickC(P)):Print("c {V}")
    for(V:=PickC(Q)):Print("c {V}")
    for(V:=PickR(S,P)):Print("r {V}")
    for(V:=PickA(Q)):Print("a {V}")
    for(V:=PickT(S,P)):Print("t {V} {S.N}")
    for(V:=PickT(S,Q)):Print("t {V} {S.N}")
    for(V:=PickTwice(S,P)):Print("w {V} {S.N}")
    Print("state {S.N}")
