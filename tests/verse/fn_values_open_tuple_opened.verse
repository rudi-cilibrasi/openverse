Id(X:t where t:type):t=X
Bind(X:t,Y:u where t:type,u:type):type{_(:t,:u):tuple(t,u)}=Id
root(t:type):=class{V:t}
extra(a:type,b:type):=class(root(a)){Other:b}
Use(P:root(t) where t:type):void=
    if(D:=extra[P]):
        F:=Bind(D.V,D.Other)
        R:=F(D.V,D.Other)
        Print("opened {array{R(1)}.Length}")
    else:
        Print("base")
Main():void=
    Use(extra(int,string){V:=3,Other:="s"})
    Use(extra(string,int){V:="s",Other:=4})
    Use(root(int){V:=1})
