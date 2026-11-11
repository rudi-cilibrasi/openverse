root(t:type):=class:
    V:t
extra(a:type,b:type):=class(root(a)):
    Other:b
    Same(X:u where u:type):u=X
Bind(B:extra(a,b),X:v where a:type,b:type,v:type):type{_(:v):v}=B.Same
Use(P:root(t) where t:type):void=
    if(D:=extra[P]):
        F:=Bind(D,D.Other)
        R:=array{F(D.Other),D.Other}
        Print("opened {R.Length}")
    else:
        Print("base")
Main():void=
    Use(extra(int,string){V:=3,Other:="s"})
    Use(extra(string,int){V:="s",Other:=4})
    Use(root(int){V:=1})
