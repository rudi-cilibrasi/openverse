expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
Rows(E:expr(t) where t:type):[]t=for(N:=1..2,V:=if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then((L.V,R.V)|(L.V+1,R.V))else E.Eval()){V}
Main():void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(Values:=Rows(P);false?)then Print("wrong")
    Print("final {P.L.Eval()}")
