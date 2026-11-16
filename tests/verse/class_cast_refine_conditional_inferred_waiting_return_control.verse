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
Rows(X:t,Mark:logic where t:type)<suspends>:t=
    defer:Print("source")
    for(N:=1..2){if(Mark?)then Print("prefix");defer{Print("leave")};Sleep(0.001);return X}
    X
Main()<suspends>:void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    Saved:=P.L.Eval()
    set P.L=lit{V:=99}
    V:=Rows((Saved,P.R.Eval()),true)
    Print("{V(0)} {V(1)}")
    I:=Rows(5,false)
    Print("int {I}")
    S:=Rows("ok",false)
    Print("string {S}")
    Print("final {P.L.Eval()}")
