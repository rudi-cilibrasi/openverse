box(t:type):=class:
    V:t
    Same(X:u where u:type)<suspends>:u=block{Sleep(0.0);X}
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){}
Use(B:box(v),P:pair(a,b) where v:type,a:type,b:type)<suspends>:[]b=
    F:type{_(:b)<suspends>:b}=B.Same
    for(A:b=if(D:=dup[P])then(D.A|D.B)else P.B):
        F(A)
Main()<suspends>:void=
    R:=Use(box(string){V:="s"},dup(int){A:=1,B:=2})
    for(V:R):Print("value {V}")
    S:=Use(box(int){V:=7},pair(int,string){A:=3,B:="s"})
    for(V:S):Print("value {V}")
