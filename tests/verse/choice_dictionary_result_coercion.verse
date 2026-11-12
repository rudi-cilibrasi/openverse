# Expected results must not widen the dictionary's already fixed type arguments.
base:=class<unique>{}
ca:=class(base):
    Me()<computes>:ca=Self
    Fixed()<computes>:ca=Self
cb:=class(base):
    Me()<computes>:cb=Self
other:=class:
    Target:ca
    Fixed()<computes>:ca=Target
Dup(X:t where t:type)<computes>:t=X|X
Same(X:t,?Y:t=X where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0
Erased(P:ca,Q:cb)<computes>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q)),B:=(Dup(1)|Dup("s"))):
        Ignore:any=A.Me()
        Same(A)+Same(B)
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Sum
Fixed(P:ca,Q:other)<computes>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q)),B:=(Dup(1)|Dup("s"))):
        R:base=A.Fixed()
        Ignore:any=A.Fixed()
        Same(R)+Same(B)
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Sum
Main():void=
    P:=ca{}
    Q:=cb{}
    Print("{Erased(P,Q)}")
    Print("{Fixed(P,other{Target:=P})}")
