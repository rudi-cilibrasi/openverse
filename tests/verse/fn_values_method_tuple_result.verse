box(t:type):=class:
    V:t
    Empty(N:int where u:type):[]u=array{}
    Id(X:u where u:type)<computes>:u=X
Bind(B:box(t) where t:type):type{_(:tuple(int)):[]t}=B.Empty
Main():void=
    F:=Bind(box(string){V:="s"})
    I:type{_(:int)<computes>:tuple(int)}=box(string){V:="s"}.Id
    Print("{F(I(7)).Length}")
