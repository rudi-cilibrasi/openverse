vehicle:=class<allocates><unique>{N:int=7}
car:=class<allocates>(vehicle){Name:string="precise"}
ca(a:subtype(vehicle)):=class<computes>:
    K:int=0
    Apply(X:u where u:subtype(a))<computes>:int=if(X=X)then X.N else 0
cb(a:subtype(vehicle)):=class<computes>:
    K:rational=0
    Apply(X:u where u:subtype(a))<computes>:int=if(X=X)then X.N else 0
Dup(X:t where t:type)<computes>:t=X|X
Run(X:t where t:subtype(vehicle))<computes>:t=
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
