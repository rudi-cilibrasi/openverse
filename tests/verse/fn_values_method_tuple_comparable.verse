token:=class<unique>{N:int}
box(t:type):=class:
    V:t
    Id(X:u where u:subtype(comparable))<computes>:u=X
Bind(B:box(t),X:a,Y:b where t:type,a:subtype(comparable),b:subtype(comparable))<computes>:type{_(:a,:b)<computes>:tuple(a,b)}=B.Id
Main():void=
    X:=token{N:=7}
    F:=Bind(box(string){V:="tag"},X,3)
    R:=F(X,9)
    if(R(0)=X)then Print("{R(0).N} {R(1)}")else Print("wrong")
