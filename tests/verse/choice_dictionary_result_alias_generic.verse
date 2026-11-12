# Aliases of method results retain distinct receiver/result columns and generic field equations.
ra(t:subtype(comparable)):=class<computes>{V:t;Items:[]t;Me()<computes>:ra(t)=Self}
rb(t:subtype(comparable)):=class<computes>{V:t;Items:[]t;Me()<computes>:rb(t)=Self}
a(t:subtype(comparable)):=class:
    V:t
    Items:[]t
    Me(Ignored:u where u:type)<computes>:ra(t)=ra(t){V:=V,Items:=Items}
b(t:subtype(comparable)):=class:
    V:t
    Items:[]t
    Me(Ignored:u where u:type)<computes>:rb(t)=rb(t){V:=V,Items:=Items}
Dup(X:t where t:type)<computes>:t=X|X
Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0
Keep(X:t where t:subtype(comparable))<computes>:int=if(X=X)then 1 else 0
Use(P:a(t),Q:b(t),X:t where t:subtype(comparable))<computes>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q)),Alias:=A,B:=(Dup(1)|Dup("s"))):
        Captured:=Alias.Me(B)
        Saved:=Captured
        if(Scoped:=Saved,Scoped.Items.Length>0)then Equal(Scoped.V,X)+Equal(Scoped.Me().V,X)+Scoped.Me().Items.Length+Keep(B) else 0
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Sum
Main():void=
    Print("{Use(a(int){V:=7,Items:=array{7}},b(int){V:=7,Items:=array{7}},7)}")
    Print("{Use(a(string){V:="s",Items:=array{"s"}},b(string){V:="s",Items:=array{"s"}},"s")}")
