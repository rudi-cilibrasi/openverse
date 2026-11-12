# Generic field and method result types retain their equations with the caller.
a(t:subtype(comparable)):=class:
    V:t
    Items:[]t
    Me()<computes>:a(t)=Self
b(t:subtype(comparable)):=class:
    V:t
    Items:[]t
    Me()<computes>:b(t)=Self
Dup(X:t where t:type)<computes>:t=X|X
Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0
Keep(X:t where t:subtype(comparable))<computes>:int=if(X=X)then 1 else 0
Use(P:a(t),Q:b(t),X:t where t:subtype(comparable))<computes>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q)),B:=(Dup(1)|Dup("s"))):
        Equal(A.V,X)+Equal(A.Me().V,X)+A.Me().Items.Length+Keep(B)
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Sum
Main():void=
    Print("{Use(a(int){V:=7,Items:=array{7}},b(int){V:=7,Items:=array{7}},7)}")
    Print("{Use(a(string){V:="s",Items:=array{"s"}},b(string){V:="s",Items:=array{"s"}},"s")}")
