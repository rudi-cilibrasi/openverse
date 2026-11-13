vehicle:=class<computes>{N:int=7}
car:=class<computes>(vehicle){Name:string="precise"}
ca:=class<computes>:
    K:int=0
    Apply(X:car)<computes>:int=X.N
cb:=class<computes>:
    K:rational=0
    Apply(X:car)<computes>:int=X.N
Dup(X:t where t:type)<computes>:t=X|X
Run(X:car)<computes>:car=
    P:=ca{}
    Q:=cb{}
    Rows:=for(A:=(Dup(P)|Dup(Q))):A.Apply(X)
    var Sum:int=0
    for(V:Rows):set Sum+=V
    Print("values {Rows.Length} {Sum}")
    X
Main():void=
    R:=Run(car{})
    Print("{R.Name} {R.N}")
