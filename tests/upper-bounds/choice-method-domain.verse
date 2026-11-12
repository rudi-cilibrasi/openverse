vehicle:=class<computes>{}
car:=class<computes>(vehicle){}
ca:=class<computes>:
    K:int=0
    Apply(X:u where u:subtype(car))<computes>:int=7
cb:=class<computes>:
    K:rational=0
    Apply(X:u where u:subtype(car))<computes>:int=7
Dup(X:t where t:type)<computes>:t=X|X
Run(X:t where t:subtype(car))<computes>:[]int=
    for(A:=(Dup(ca{})|Dup(cb{}))):A.Apply(X)
Main():void=
    Rows:=Run(car{})
    var Sum:int=0
    for(V:Rows):set Sum+=V
    Print("values {Rows.Length} {Sum}")
