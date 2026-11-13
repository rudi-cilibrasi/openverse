ca(a:type):=class<computes>:
    Apply(X:u where u:subtype(a))<computes>:a=X
cb(a:type):=class<computes>:
    Apply(X:u where u:subtype(a))<computes>:a=X
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    P:=ca(int){}
    Q:=cb(int){}
    Rows:=for(A:=(Dup(P)|Dup(Q))):A.Apply(7)
    var Sum:int=0
    for(V:Rows):set Sum+=V
    Print("values {Rows.Length} {Sum}")
