vehicle:=class<computes>{N:int=7}
car:=class<computes>(vehicle){Name:string="precise"}
ca(a:subtype(vehicle)):=class<computes>:
    K:int=0
    Apply(X:u where u:subtype(a))<computes>:int=X.N
cb(a:subtype(car)):=class<computes>:
    K:rational=0
    Apply(X:u where u:subtype(a))<computes>:int=X.N
Dup(X:t where t:type)<computes>:t=X|X
Run(X:t where t:subtype(car))<computes>:t=
    P:=ca(t){}
    Q:=cb(t){}
    Rows:=for(A:=(Dup(P)|Dup(Q))):A.Apply(X)
    var Sum:int=0
    for(V:Rows):set Sum+=V
    Print("values {Rows.Length} {Sum}")
    X
Main():void=
    R:=Run(car{})
    Print("{R.Name} {R.N}")
