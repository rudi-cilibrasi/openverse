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
Pick(S:Cell,E:Expr(t),Fallback:t where t:type)<transacts>:t=
    for(V:=if(Choose[S,true], P:=Pair[E])then (P.Eval()|P.Eval()) else E.Eval()):
        K:=0|1
        defer:Cleanup(S,1,K)
        if(K=1):return V
        Print("advance {S.N}")
    Fallback
Main()<transacts>:void=
    P:=Pair(int,int){L:=Lit{V:=3},R:=Lit{V:=7}}
    S:=Cell{}
    for(V:=Pick(S,P,(99,99))):Print("all {V(0)} {V(1)}")
    Print("state {S.N}")
    F:=Cell{}
    for(V:=Pick(F,PlainPair{},(99,99))):Print("all {V(0)} {V(1)}")
    Print("state {F.N}")
    Reject:=Cell{}
    if(V:=Pick(Reject,P,(99,99)),V(0)=9999)then Print("bad")else Print("reject {Reject.N}")
