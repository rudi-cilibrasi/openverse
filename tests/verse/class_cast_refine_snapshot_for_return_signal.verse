expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
ReturnFor(E:expr(t),Ev:event(int),Stop:logic where t:type):[]t =
    Ignored:[]t=for(K:=0..1,Printed:=block{Print("prefix");0},P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{set P.L=lit{V:=99};0},R:=lit[P.R],J:=(0|1)):
        Ev.Signal(1)
        if(Stop?)then return array{(L.V,R.V)}
        (L.V,R.V)
    array{}
Main():void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=4}}
    E:=event(int){}
    Values:=ReturnFor(P,E,true)
    for(V:Values){Print("return signal {V(0)} {V(1)} {P.L.Eval()}")}
