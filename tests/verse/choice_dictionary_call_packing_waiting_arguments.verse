cell:=class{var N:int=0}
ma:=class:
    H:cell
    Tag:string
    var Count:int
    Stamp()<transacts>:int=block{Print("default {Tag} {Count}");set H.N+=10;Count}
    M(X:int,Y:int,?Z:int=Stamp())<transacts>:int=
        Print("method {Tag} {X} {Y} {Z}")
        set H.N+=100
        set Count+=1
        X+Y+Z
mb:=class:
    H:cell
    Tag:string
    var Count:int
    Stamp()<transacts>:int=block{Print("default {Tag} {Count}");set H.N+=10;Count}
    M(X:int,Y:int,?Z:int=Stamp())<transacts>:int=
        Print("method {Tag} {X} {Y} {Z}")
        set H.N+=100
        set Count+=1
        X+Y+Z
ca:=class:
    H:cell
    var Child:ma
    Original:ma
    Other:ma
    Args(E:event(void))<transacts><suspends>:tuple(int,int)=
        defer:Print("leave args a")
        Print("wait a")
        set H.N+=1
        E.Await()
        Print("args a")
        set Original.Count=30
        set Child=Other
        (1,2)
cb:=class:
    H:cell
    var Child:mb
    Original:mb
    Other:mb
    Args(E:event(void))<transacts><suspends>:tuple(int,int)=
        defer:Print("leave args b")
        Print("wait b")
        set H.N+=1
        E.Await()
        Print("args b")
        set Original.Count=50
        set Child=Other
        (4,5)
Dup(X:t where t:type)<computes>:t=X|X
Use(H:cell,E:event(void),P:ca,Q:cb)<suspends>:int=
    var Total:int=0
    defer:Print("source {Total} {H.N}")
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        V:=A.Child.M(A.Args(E))
        set Total+=1
        Print("row {V} {H.N}")
        V
    Rows.Length
Main()<suspends>:void=
    H:=cell{}
    E:=event(void){}
    P0:=ma{H:=H,Tag:="a0",Count:=10}
    P1:=ma{H:=H,Tag:="a1",Count:=20}
    Q0:=mb{H:=H,Tag:="b0",Count:=40}
    Q1:=mb{H:=H,Tag:="b1",Count:=40}
    P:=ca{H:=H,Child:=P0,Original:=P0,Other:=P1}
    Q:=cb{H:=H,Child:=Q0,Original:=Q0,Other:=Q1}
    Cancelled:=race:
        Use(H,E,P,Q)
        block{Sleep(0.05);-1}
    Print("cancel {Cancelled} {H.N}")
    if(H.N=1,P0.Count=10,P1.Count=20,Q0.Count=40,Q1.Count=40)then Print("cancel state ok") else Print("bad cancel state")
    H2:=cell{}
    E2:=event(void){}
    P20:=ma{H:=H2,Tag:="a0",Count:=10}
    P21:=ma{H:=H2,Tag:="a1",Count:=20}
    Q20:=mb{H:=H2,Tag:="b0",Count:=40}
    Q21:=mb{H:=H2,Tag:="b1",Count:=40}
    P2:=ca{H:=H2,Child:=P20,Original:=P20,Other:=P21}
    Q2:=cb{H:=H2,Child:=Q20,Original:=Q20,Other:=Q21}
    T:=spawn{Use(H2,E2,P2,Q2)}
    Sleep(0.1)
    E2.Signal()
    Print("signal 1")
    Sleep(0.1)
    E2.Signal()
    Print("signal 2")
    Sleep(0.1)
    E2.Signal()
    Print("signal 3")
    Sleep(0.1)
    E2.Signal()
    Print("signal 4")
    Result:=T.Await()
    Print("done {Result} {H2.N}")
    if(P20.Count=30,P21.Count=21,Q20.Count=50,Q21.Count=41)then Print("state ok") else Print("bad state")
