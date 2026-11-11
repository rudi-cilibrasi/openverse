source(t:type):=interface:
    Get():t
    Pair(X:u where u:type):tuple(t,u)=(Get(),X)
    Empty(N:int where u:type):[]u=array{}
mixed(a:type,b:type):=class(source([]b)):
    Extra:a
    V:b
    Get<override>():[]b=array{V}
Use(P:source(t),X:u where t:type,u:type):tuple(t,u,int)=
    F:type{_(:u):tuple(t,u)}=P.Pair
    G:type{_(:int):[]u}=P.Empty
    R:=F(X)
    (R(0),R(1),G(0).Length)
Main():void=
    R:=Use(mixed(int,string){Extra:=4,V:="s"},7)
    Print("{R(0).Length} {R(1)} {R(2)}")
