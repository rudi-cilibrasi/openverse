expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
Rows(E:expr(t),Count:int where t:type):t=
    Values:=for(N:=1..Count,V:=if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then((L.V,R.V)|(L.V+1,R.V))else E.Eval()){if(N=2)then return V;array{array{}}}
    Witness:[][][]int=Values
    Print("rows {Witness.Length}")
    E.Eval()
Main():void=
    for(Count:=1..2):
        P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
        V:=Rows(P,Count)
        Print("{V(0)} {V(1)}")
        Print("final {P.L.Eval()}")
