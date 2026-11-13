# set A.State.X += A.RHS(E), whose RHS waits and then replaces State: the old value is read after it
# returns; a cancelled one stores nothing
cell:=class{var N:int=0}
sa:=struct{X:int;Tail:int}
sb:=struct{X:rational;Tail:int}
ca:=class:
    H:cell
    var State:sa
    RHS(E:event(int))<transacts><suspends>:int=
        defer:Print("leave a")
        Print("wait a")
        set H.N+=1
        V:=E.Await()
        Print("resume a {V}")
        set H.N+=10
        set State=sa{X:=100,Tail:=200}
        V
cb:=class:
    H:cell
    var State:sb
    RHS(E:event(int))<transacts><suspends>:int=
        defer:Print("leave b")
        Print("wait b")
        set H.N+=1
        V:=E.Await()
        Print("resume b {V}")
        set H.N+=10
        set State=sb{X:=100,Tail:=200}
        V
Dup(X:t where t:type)<computes>:t=X|X
Use(H:cell,E:event(int),P:ca,Q:cb)<suspends>:int=
    var Total:int=0
    defer:Print("source {Total} {H.N}")
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        V:=set A.State.X+=A.RHS(E)
        set Total+=1
        Print("body {H.N}")
        0
    Rows.Length
Main()<suspends>:void=
    if(Half:=1/2):
        H:=cell{}
        E:=event(int){}
        P:=ca{H:=H,State:=sa{X:=1,Tail:=2}}
        Q:=cb{H:=H,State:=sb{X:=Half,Tail:=2}}
        R:=race:
            Use(H,E,P,Q)
            block{Sleep(0.05);-1}
        Print("cancel {R} {H.N}")
        if(P.State.X=1,Q.State.X=Half,P.State.Tail=2,Q.State.Tail=2)then Print("cancel state ok") else Print("bad cancel state")
        H2:=cell{}
        E2:=event(int){}
        P2:=ca{H:=H2,State:=sa{X:=1,Tail:=2}}
        Q2:=cb{H:=H2,State:=sb{X:=Half,Tail:=2}}
        T:=spawn{Use(H2,E2,P2,Q2)}
        Sleep(0.1)
        E2.Signal(1)
        Print("signal 1")
        Sleep(0.1)
        E2.Signal(2)
        Print("signal 2")
        Sleep(0.1)
        E2.Signal(3)
        Print("signal 3")
        Sleep(0.1)
        E2.Signal(4)
        Print("signal 4")
        Result:=T.Await()
        Print("done {Result} {H2.N}")
        if(P2.State.X=102,P2.State.Tail=200,Q2.State.X=104,Q2.State.Tail=200)then Print("state ok") else Print("bad state")
