# set A.K += A.Change(), whose RHS waits and then sets K: the old value is read after it, when it
# returns; a cancelled one stores nothing
ca:=class:
    var K:int=1
    Change()<transacts><suspends>:int=
        defer:Print("leave a")
        Sleep(0.1)
        set K=100
        3
cb:=class:
    var K:rational=0
    Change()<transacts><suspends>:int=
        defer:Print("leave b")
        Sleep(0.1)
        set K=100
        3
Dup(X:t where t:type)<computes>:t=X|X
Use(P:ca,Q:cb)<suspends>:int=
    var Total:int=0
    defer:Print("source {Total}")
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        R:=set A.K+=A.Change()
        set Total+=1
        Print("body {Total}")
        0
    Rows.Length
Main()<suspends>:void=
    if(Initial:=2/3):
        P:=ca{}
        Q:=cb{K:=Initial}
        R:=race:
            Use(P,Q)
            block{Sleep(0.25);-1}
        Print("done {R} {P.K} {Floor(Q.K)}")
        if(Q.K=2/3)then Print("ratio ok") else Print("bad ratio")
        P2:=ca{}
        Q2:=cb{K:=Initial}
        R2:=Use(P2,Q2)
        Print("done {R2} {P2.K} {Floor(Q2.K)}")
        if(Q2.K=103)then Print("ratio ok") else Print("bad ratio")
