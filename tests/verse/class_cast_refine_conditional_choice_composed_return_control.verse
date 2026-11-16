expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
Rows(E:expr(tuple(int,int)),Other:expr(tuple(int,int))):[]tuple(tuple(int,int),tuple(int,int))=
    Values:[]tuple(tuple(int,int),tuple(int,int))=for(N:=1..2,V:=if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then((L.V,R.V)|(L.V+1,R.V))else E.Eval(),W:=if(Print("second"),Q:=vpair[Other],SavedQ:=Q.L,LQ:=lit[SavedQ],set Q.L=lit{V:=99},RQ:=lit[Q.R])then((LQ.V,RQ.V)|(LQ.V+1,RQ.V))else Other.Eval()){if(N=2)then return array{(V,W)};(V,W)}
    Values
Main():void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    Q:=vpair(int,int){L:=lit{V:=5},R:=lit{V:=9}}
    Values:=Rows(P,Q)
    for(V:Values){Print("{V(0)(0)} {V(0)(1)} {V(1)(0)} {V(1)(1)}")}
    Print("final {P.L.Eval()} {Q.L.Eval()}")
