# Dictionary results must retain their equation with the original receiver.
base:=class<unique>:
    Me()<computes>:base=Self
ca:=class(base):
    Me<override>()<computes>:ca=Self
cb:=class(base):
    Me<override>()<computes>:cb=Self
ga(t:subtype(comparable)):=class:
    V:t
    Value()<computes>:t=V
gb(t:subtype(comparable)):=class:
    V:t
    Value()<computes>:t=V
Dup(X:t where t:type)<computes>:t=X|X
Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0
Same(X:t,?Y:t=X where t:subtype(comparable))<computes>:int=Equal(X,Y)
Run(P:ca,Q:cb)<computes>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q)),B:=(Dup(1)|Dup("s"))):
        R:=A.Me()
        (R,B,Equal(A,R)+Same(R)+Same(B))
    var Sum:int=0
    for(Row:Rows):set Sum+=Row(2)
    Rows.Length*100+Sum
Generic(P:ga(t),Q:gb(t),X:t where t:subtype(comparable))<computes>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q)),B:=(Dup(1)|Dup("s"))):
        R:=A.Value()
        (A,R,Equal(R,X)+Same(R)+Same(B))
    var Sum:int=0
    for(Row:Rows):set Sum+=Row(2)
    Rows.Length*100+Sum
Main():void=
    Print("{Run(ca{},cb{})}")
    X:=Generic(ga(int){V:=7},gb(int){V:=7},7)
    Y:=Generic(ga(string){V:="s"},gb(string){V:="s"},"s")
    Print("{X} {Y}")
