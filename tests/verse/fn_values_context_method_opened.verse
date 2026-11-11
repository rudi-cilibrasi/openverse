cell:=class{var N:int=0}
Tick(C:cell,Tag:string):int=
    set C.N+=1
    Print("{Tag} {C.N}")
    C.N
Arg(C:cell,X:t where t:type):t=
    N:=Tick(C,"arg")
    X
root(t:type):=class:
    V:t
    C:cell
    N:int
    Id(X:u where u:subtype(comparable))<computes>:u=X
extra(a:subtype(comparable),b:subtype(comparable)):=class(root(a)){Other:b}
Touch(B:root(t) where t:type):root(t)=
    N:=Tick(B.C,"receiver")
    B
Bind(B:root(t),X:a,Y:b where t:type,a:subtype(comparable),b:subtype(comparable))<computes>:type{_(:a,:b)<computes>:tuple(a,b)}=B.Id
Twice(F:type{_(:a,:b)<computes>:tuple(a,b)},X:a,Y:b where a:subtype(comparable),b:subtype(comparable))<computes>:tuple(a,b)=F(X,Y)|F(X,Y)
Use(P:root(t) where t:type):void=
    if(D:=extra[P]):
        R:=for(V:=Twice(Touch(D).Id,D.V,D.Other)):
            if(V(0)=D.V,V(1)=D.Other)then 1 else 0
        Print("opened {D.N} {R.Length}")
    else:
        Print("base {P.N}")
Main():void=
    Use(extra(string,int){V:="input",Other:=3,C:=cell{},N:=4})
    Use(root(int){V:=7,C:=cell{},N:=5})
