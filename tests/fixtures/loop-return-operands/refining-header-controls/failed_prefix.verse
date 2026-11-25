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
Cell:=class{var N:int=0}
Choose(S:Cell,Pass:logic)<transacts><decides>:void=
    set S.N+=1000
    Pass?
Cleanup(S:Cell,V:int,Y:int)<transacts>:void=
    set S.N+=10
    Print("cleanup {V} {Y} {S.N}")
Pick(S:Cell,Pass:logic,E:Expr(t) where t:type)<transacts>:int=
    if(Choose[S,Pass]):
        Vs:=if(Choose[S,true], P:=Pair[E], X:=Lit[P.L])then array{X.V,1} else array{4,1}
        for(V:Vs):
            Y:=V|V+100
            defer:Cleanup(S,V,Y)
            if(V=1):return Y|Y+1000
            Print("advance {V} {Y} {S.N}")
    S.N
Main()<transacts>:void=
    P:=Pair(int,int){L:=Lit{V:=3},R:=Lit{V:=7}}
    S0:=Cell{}
    for(V:=Pick(S0,true,P)):Print("all {V}")
    Print("state {S0.N}")
    F0:=Cell{}
    if(V:=Pick(F0,true,P),V=101)then Print("first {V}")else Print("missed")
    Print("state {F0.N}")
    R0:=Cell{}
    if(V:=Pick(R0,true,P),V=9999)then Print("bad")else Print("reject {R0.N}")
    S1:=Cell{}
    for(V:=Pick(S1,false,P)):Print("all {V}")
    Print("state {S1.N}")
    F1:=Cell{}
    if(V:=Pick(F1,false,P),V=101)then Print("first {V}")else Print("missed")
    Print("state {F1.N}")
    R1:=Cell{}
    if(V:=Pick(R1,false,P),V=9999)then Print("bad")else Print("reject {R1.N}")
    S2:=Cell{}
    for(V:=Pick(S2,true,PlainPair{})):Print("all {V}")
    Print("state {S2.N}")
    F2:=Cell{}
    if(V:=Pick(F2,true,PlainPair{}),V=101)then Print("first {V}")else Print("missed")
    Print("state {F2.N}")
    R2:=Cell{}
    if(V:=Pick(R2,true,PlainPair{}),V=9999)then Print("bad")else Print("reject {R2.N}")
