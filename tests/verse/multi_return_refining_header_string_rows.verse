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
Base:=class{B:int=2}
Der:=class(Base){K:int=3}
Cell:=class{var N:int=0}
Choose(S:Cell,Pass:logic)<transacts><decides>:void=
    set S.N+=1000
    Pass?
Cleanup(S:Cell,V:int,Y:int)<transacts>:void=
    set S.N+=10
    Print("cleanup {V} {Y} {S.N}")
Pick(S:Cell,E:Expr(t) where t:type)<transacts>:string=
    for(V:=if(Choose[S,true], P:=Pair[E], X:=Lit[P.L])then ("lit {X.V} {S.N}"|"a") else ("plain {S.N}"|"b")):
        defer:Cleanup(S,V.Length,0)
        if(V.Length=1):return "{V}!"|"{V}?"
        Print("advance {V} {S.N}")
    "none"
Main()<transacts>:void=
    P:=Pair(int,int){L:=Lit{V:=3},R:=Lit{V:=7}}
    S:=Cell{}
    for(V:=Pick(S,P)):Print("all {V}")
    Print("state {S.N}")
    T:=Cell{}
    for(V:=Pick(T,PlainPair{})):Print("all {V}")
    Print("state {T.N}")
