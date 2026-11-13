Id(X:t where t:type)<computes>:t=X
Wait(X:t where t:type)<suspends>:t=
    Sleep(0.01)
    X
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){}
Use(P:pair(a,b) where a:type,b:type)<suspends>:[]b=
    F:type{_(:b)<suspends>:b}=Wait
    G:type{_(:b)<computes>:b}=Id
    for(A:b=if(D:=dup[P])then(D.A|D.B)else P.B):
        F(G(A))
Main()<suspends>:void=
    R:=Use(dup(int){A:=1,B:=2})
    for(V:R):Print("value {V}")
    S:=Use(pair(int,string){A:=3,B:="s"})
    for(V:S):Print("value {V}")
