cell:=class{var N:int=0}
source(t:type):=interface:
    Get():t
    Id(X:u where u:subtype(comparable)):u=X
root(t:type):=class(source(t)):
    V:t
    N:int
    Get<override>():t=V
extra(a:subtype(comparable),b:subtype(comparable)):=class(root(a)){Other:b}
Bind(B:source(c),X:a,Y:b where c:type,a:subtype(comparable),b:subtype(comparable)):type{_(:a,:b):tuple(a,b)}=B.Id
Use(P:root(t) where t:type):void=
    if(D:=extra[P]):
        F:=Bind(D,D.V,D.Other)
        R:=F(D.V,D.Other)
        if(R(0)=D.V,R(1)=D.Other)then Print("opened {D.N}")else Print("wrong")
    else:
        Print("base {P.N}")
Main():void=
    Use(extra(string,int){V:="old",Other:=22,N:=7})
    Use(extra(int,string){V:=22,Other:="new",N:=8})
    Use(root(int){V:=3,N:=9})
