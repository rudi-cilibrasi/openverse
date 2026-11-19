expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
ReturnCleanup(E:expr(t) where t:type)<transacts>:?t =
    var N:int=0
    defer:
        Print("outer return {N}")
    if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then block:
        defer:
            set N+=1
            Print("inner return {N}")
        set N=L.V
        return option{(L.V,R.V)}
    false
BreakCleanup(E:expr(t) where t:type):int =
    var N:int=0
    defer:
        Print("outer break {N}")
    loop:
        if(Print("prefix"),P:=vpair[E],Saved:=P.L,L:=lit[Saved],set P.L=lit{V:=99},R:=lit[P.R])then block:
            defer:
                set N+=1
                Print("inner break {N}")
            set N=L.V
            break
        break
    N
Main():void=
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=4}}
    if(V:=ReturnCleanup(P)?)then Print("return {V(0)} {V(1)}")else Print("wrong")
    Q:=vpair(int,int){L:=lit{V:=5},R:=lit{V:=6}}
    Print("break {BreakCleanup(Q)}")
