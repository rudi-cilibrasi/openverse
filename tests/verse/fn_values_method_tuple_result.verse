box(t:type):=class:
    V:t
    Empty(N:u where u:type):[]u=array{}
    Id(X:u where u:type)<computes>:u=X
Bind(B:box(t) where t:type):type{_(:tuple(t)):[]tuple(t)}=B.Empty
Main():void=
    F:=Bind(box(string){V:="s"})
    I:type{_(:string)<computes>:tuple(string)}=box(string){V:="s"}.Id
    Print("{F(I("x")).Length}")
