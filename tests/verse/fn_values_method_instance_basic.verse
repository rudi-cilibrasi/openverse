box(t:type):=class:
    var V:t
    Generic(X:u where u:type):u=X
    Pair(X:u where u:type):tuple(t,u)=(V,X)
Bind(B:box(u) where u:type):type{_(:int):tuple(u,int)}=B.Pair
Run(B:box(t),X:v where t:type,v:type):tuple(t,v)=
    F:type{_(:v):v}=B.Generic
    G:type{_(:v):tuple(t,v)}=B.Pair
    G(F(X))
Main():void=
    B:=box(string){V:="before"}
    F:=Bind(B)
    set B.V="after"
    R:=F(7)
    S:=Run(box(int){V:=3},"s")
    Print("{R(0)} {R(1)} {S(0)} {S(1)}")
