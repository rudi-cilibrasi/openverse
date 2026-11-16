# expect: this call may signal an event
expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
Send(E:expr(t),Ev:event(int) where t:type)<transacts>:?t =
    if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R],Ev.Signal(1))then block:
        Ev.Signal(1)
        option{(L.V,R.V)}
    else false
Main():void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=4}}
    Ev:=event(int){}
    Value:=Send(P,Ev)
    if(V:=Value?)then Print("signal {V(0)} {V(1)} {P.L.Eval()}")else Print("wrong")
