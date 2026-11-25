Expr(t:type) := class<abstract>:
    Eval()<computes>:t
Lit := class(Expr(int)):
    V:int
    Eval<override>()<computes>:int=V
Pair(a:type,b:type) := class(Expr(tuple(a,b))):
    L:Expr(a)
    R:Expr(b)
    Eval<override>()<computes>:tuple(a,b)=(L.Eval(),R.Eval())
One()<computes>:int=11
Two()<computes>:int=22
Produce(E:Expr(t),F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int where t:type)<computes>:type{_()<computes>:int}=
    for(G:=if(P:=Pair[E], X:=Lit[P.L])then (Dummy|F) else (F|F)):
        if(N=3):return G|G
    F|F
Caller(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    E:=Pair(int,int){L:=Lit{V:=3},R:=Lit{V:=7}}
    Rows:=for(G:=Produce(E,F,Dummy,3)):
        Print("got {G()}")
        1
    Rows.Length
Main():void=Print("count {Caller(One,Two)}")
