expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
PairValues(A:int,B:int)<computes>:tuple(int,int)=(A,B)|(A+1,B)
Rows(E:expr(t) where t:type):[]t=for(N:=1..2,V:=if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then {defer{Print("branch cleanup")};Print("branch");PairValues(L.V,R.V)}else E.Eval()){V}
Main():void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    for(V:Rows(P)){Print("{V(0)} {V(1)}")}
    Print("final {P.L.Eval()}")
