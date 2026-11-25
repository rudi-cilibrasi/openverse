Expr(t:type) := class<abstract>:
    Eval()<transacts>:t
Lit := class(Expr(int)):
    V:int
    Eval<override>()<transacts>:int=V
Pair(a:type,b:type) := class(Expr(tuple(a,b))):
    var L:Expr(a)
    R:Expr(b)
    Eval<override>()<transacts>:tuple(a,b)=(L.Eval(),R.Eval())
PlainPair:=class(Expr(tuple(int,int))):
    Eval<override>()<transacts>:tuple(int,int)=(4,8)
Cell:=class{var N:int=0}
Choose(S:Cell,Pass:logic)<transacts><decides>:void=
    set S.N+=1000
    Pass?
Replace(E:Expr(t) where t:type)<transacts>:void=
    if(P:=Pair[E], L:=Lit[P.L]):
        set P.L=Lit{V:=99}
Cleanup(S:Cell,V:int,Y:int)<transacts>:void=
    set S.N+=10
    Print("cleanup {V} {Y} {S.N}")
Pick(S:Cell,E:Expr(t) where t:type)<transacts>:int=
    for(V:=if(Choose[S,true], P:=Pair[E], X:=Lit[P.L])then (X.V|X.V-2) else (4|1)):
        Y:=V|V+100
        defer:Cleanup(S,V,Y)
        if(V=1):return Y|Y+1000
        Replace(E)
        Print("advance {V} {Y} {S.N}")
    S.N
Main()<transacts>:void=
    P:=Pair(int,int){L:=Lit{V:=3},R:=Lit{V:=7}}
    S:=Cell{}
    for(V:=Pick(S,P)):Print("all {V}")
    Print("state {S.N}")
    First:=Cell{}
    if(V:=Pick(First,PlainPair{}),V=101)then Print("first {V}")else Print("missed")
    Print("state {First.N}")
    Print("mutated {P.L.Eval()}")
