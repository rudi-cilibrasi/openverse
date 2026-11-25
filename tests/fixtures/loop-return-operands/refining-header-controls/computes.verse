Expr(t:type) := class<abstract>:
    Eval():t
Lit := class(Expr(int)):
    V:int
    Eval<override>():int=V
Pair(a:type,b:type) := class(Expr(tuple(a,b))):
    L:Expr(a)
    R:Expr(b)
    Eval<override>():tuple(a,b)=(L.Eval(),R.Eval())
PlainPair:=class(Expr(tuple(int,int))):
    Eval<override>():tuple(int,int)=(4,8)
Pick(E:Expr(t) where t:type)<computes>:int=
    Vs:=if(P:=Pair[E], X:=Lit[P.L])then array{X.V,1} else array{4,1}
    for(V:Vs):
        Y:=V|V+100
        if(V=1):return Y|Y+1000
        Y
    99
Main():void=
    P:=Pair(int,int){L:=Lit{V:=3},R:=Lit{V:=7}}
    for(V:=Pick(P)):Print("all {V}")
    if(V:=Pick(PlainPair{}),V=101)then Print("first {V}")else Print("missed")
