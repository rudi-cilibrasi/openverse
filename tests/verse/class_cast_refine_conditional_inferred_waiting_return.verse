expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
text:=class(expr(string)):
    V:string
    Eval<override>():string=V
Rows(E:expr(t) where t:type)<suspends>:t=
    defer:Print("source")
    for(N:=1..2,V:=if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then((L.V,R.V)|(L.V+1,R.V))else E.Eval()){defer{Print("leave")};Sleep(0.001);return V}
    E.Eval()
Main()<suspends>:void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    V:=Rows(P)
    Print("{V(0)} {V(1)}")
    I:=Rows(lit{V:=5})
    Print("int {I}")
    S:=Rows(text{V:="ok"})
    Print("string {S}")
    Print("final {P.L.Eval()}")
