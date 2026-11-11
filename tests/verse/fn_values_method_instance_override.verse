root(t:type):=class:
    V:t
    Pair(X:u where u:type):tuple(t,u)=(V,X)
child(a:type,b:type):=class(root(b)):
    Extra:a
    Pair<override>(X:v where v:type):tuple(b,v)=(V,X)
Bind(P:root(u) where u:type):type{_(:int):tuple(u,int)}=P.Pair
Run(P:root(t),X:u where t:type,u:type):tuple(t,u)=
    F:type{_(:u):tuple(t,u)}=P.Pair
    F(X)
Main():void=
    C:=child(int,string){V:="old",Extra:=3}
    F:type{_(:int):tuple(string,int)}=C.Pair
    R:=F(8)
    S:=Run(C,9)
    G:=Bind(C)
    T:=G(10)
    Print("{R(0)} {R(1)} {S(1)} {T(1)}")
