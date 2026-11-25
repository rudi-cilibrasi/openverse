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
Holder:=class:
    Base:int=10
    Pick(S:Cell,E:Expr(t) where t:type)<transacts>:int=
        Vs:=if(Choose[S,true], P:=Pair[E], X:=Lit[P.L])then array{X.V+Base,1} else array{Base+4,1}
        for(V:Vs):
            Y:=V|V+100
            defer:Cleanup(S,V,Y)
            if(V=1):return Y|Y+1000
            Print("advance {V} {Y} {S.N}")
        S.N+Base
Main()<transacts>:void=
    P:=Pair(int,int){L:=Lit{V:=3},R:=Lit{V:=7}}
    S0:=Cell{}
    for(V:=Holder{}.Pick(S0,P)):Print("all {V}")
    Print("state {S0.N}")
    F0:=Cell{}
    if(V:=Holder{}.Pick(F0,P),V=101)then Print("first {V}")else Print("missed")
    Print("state {F0.N}")
    R0:=Cell{}
    if(V:=Holder{}.Pick(R0,P),V=9999)then Print("bad")else Print("reject {R0.N}")
    S1:=Cell{}
    for(V:=Holder{Base:=0}.Pick(S1,PlainPair{})):Print("all {V}")
    Print("state {S1.N}")
    F1:=Cell{}
    if(V:=Holder{Base:=0}.Pick(F1,PlainPair{}),V=101)then Print("first {V}")else Print("missed")
    Print("state {F1.N}")
    R1:=Cell{}
    if(V:=Holder{Base:=0}.Pick(R1,PlainPair{}),V=9999)then Print("bad")else Print("reject {R1.N}")
