root(b:type):=class<computes>{N:int=7}
vehicle:=class<computes>(root(int)){}
car:=class<computes>(vehicle){Name:string="precise"}
ca(a:subtype(root(b)),b:type):=class<computes>:
    K:int=0
    Apply(X:u where u:subtype(a))<computes>:int=X.N
cb(a:subtype(root(b)),b:type):=class<computes>:
    K:rational=0
    Apply(X:u where u:subtype(a))<computes>:int=X.N
Dup(X:t where t:type)<computes>:t=X|X
Run(X:t where b:type,t:subtype(root(b)))<computes>:t=
    P:=ca(t,b){}
    Q:=cb(t,b){}
    Rows:=for(A:=(Dup(P)|Dup(Q))):A.Apply(X)
    var Sum:int=0
    for(V:Rows):set Sum+=V
    Print("values {Rows.Length} {Sum}")
    X
Main():void=
    R:=Run(car{})
    Print("{R.Name} {R.N}")
