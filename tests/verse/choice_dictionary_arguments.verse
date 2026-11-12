# Argument evaluation remains in the caller, with correlated input columns.
cell:=class{var N:int=0}
ca:=class:
    K:int
    Take(X:ca)<computes>:int=X.K
a(t:subtype(comparable)):=class:
    V:t
    Value()<computes>:t=V
    Same(X:t)<computes>:int=if(V=X)then 1 else 0
    Pair(X:t,Y:t)<computes>:int=if(X=Y)then 1 else 0
    Empty(X:?t)<computes>:int=if(X?)then 0 else 1
cb:=class:
    K:int
    Take(X:cb)<computes>:int=X.K
b(t:subtype(comparable)):=class:
    V:t
    Value()<computes>:t=V
    Same(X:t)<computes>:int=if(V=X)then 1 else 0
    Pair(X:t,Y:t)<computes>:int=if(X=Y)then 1 else 0
    Empty(X:?t)<computes>:int=if(X?)then 0 else 1
Dup(X:t where t:type)<computes>:t=X|X
Keep(X:t,?Y:t=X where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0
Class(P:ca,Q:cb)<computes>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q)),B:=(Dup(1)|Dup("s"))):A.Take(A)+Keep(B)
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Sum
Generic(P:a(t),Q:b(t),X:t where t:subtype(comparable))<computes>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q)),B:=(Dup(1)|Dup("s"))):
        A.Same(A.Value())+A.Pair(A.Value(),X)+A.Empty(false)+Keep(B)
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Sum
Main():void=
    Print("{Class(ca{K:=1},cb{K:=2})}")
    N:=Generic(a(int){V:=7},b(int){V:=7},7)
    S:=Generic(a(string){V:="s"},b(string){V:="s"},"s")
    Print("{N} {S}")
