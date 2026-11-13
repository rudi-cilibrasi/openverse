# The old field value is read after an RHS wait; cancellation skips the store.
base:=class:
    var K:int
    Change()<transacts><suspends>:int=
        defer:Print("leave {K}")
        Sleep(0.1)
        set K=100
        3
ca:=class(base){}
cb:=class(base){}
Dup(X:t where t:type)<computes>:t=X|X
Use(P:ca,Q:cb)<suspends>:int=
    defer:Print("source {P.K} {Q.K}")
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        R:=set A.K+=A.Change()
        Print("body {R} {A.K}")
        R
    Rows.Length
Main()<suspends>:void=
    P:=ca{K:=1}
    Q:=cb{K:=2}
    R:=race:
        Use(P,Q)
        block{Sleep(0.25);-1}
    Print("done {R} {P.K} {Q.K}")
    P2:=ca{K:=1}
    Q2:=cb{K:=2}
    R2:=Use(P2,Q2)
    Print("done {R2} {P2.K} {Q2.K}")
