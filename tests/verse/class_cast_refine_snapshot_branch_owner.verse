expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
Work(E:expr(t) where t:type)<suspends>:?t =
    var Result:?t=false
    var N:int=0
    if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then block:
        branch:
            defer:
                Print("child cleanup")
            Print("child start")
            Sleep(0.1)
            set N+=L.V
            Print("child done {L.V}")
        set Result=option{(L.V,R.V)}
        Print("body")
    Print("after if")
    Sleep(0.2)
    Print("count {N}")
    Result
Main()<suspends>:void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=4}}
    Value:=Work(P)
    if(V:=Value?)then Print("async {V(0)} {V(1)}")else Print("wrong")
