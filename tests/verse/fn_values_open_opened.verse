Id(X:t where t:type):t=X
Bind(X:t where t:type):type{_(:t):t}=Id
root(t:type):=class:
    A:t
extra(a:type,b:type):=class(root(a)):
    B:b
Use(P:root(t) where t:type):void=
    if (D:=extra[P]):
        F:=Bind(D.B)
        G:=Bind(array{D.B})
        H:=Bind(D.A)
        V:=F(D.B)
        W:=H(D.A)
        Print("opened {G(array{V}).Length}")
    else:
        Print("base")
Main():void=
    Use(extra(int,string){A:=3,B:="s"})
    Use(extra(string,int){A:="a",B:=7})
    Use(root(int){A:=1})
