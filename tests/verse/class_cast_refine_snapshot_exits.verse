expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
Returns(E:expr(t) where t:type):?t =
    if (Print("prefix"), P := vpair[E], Saved := P.L, L := lit[Saved], set P.L = lit{V:=99}, R := lit[P.R]) then block:
        return option{(L.V, R.V)}
    false
Loops(E:expr(t) where t:type):int =
    var N:int=0
    loop:
        if (Print("prefix"), P := vpair[E], Saved := P.L, L := lit[Saved], set P.L = lit{V:=99}, R := lit[P.R]) then block:
            set N=L.V+R.V
            break
        break
    N
Cleanup(E:expr(t) where t:type):int =
    var N:int=0
    if (Print("prefix"), P := vpair[E], Saved := P.L, L := lit[Saved], set P.L = lit{V:=99}, R := lit[P.R]) then block:
        defer:
            set N+=1
            Print("cleanup")
        set N=L.V
        Print("body")
    else set N=40
    N
Main():void =
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=4}}
    if(V:=Returns(P)?)then Print("return {V(0)} {V(1)}")else Print("wrong")
    Q:=vpair(int,int){L:=lit{V:=5},R:=lit{V:=6}}
    Print("break {Loops(Q)}")
    R:=vpair(int,int){L:=lit{V:=7},R:=lit{V:=8}}
    Print("copy {Cleanup(R)}")
