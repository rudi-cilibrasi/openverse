ca:=class<computes>:
    Apply(X:int)<computes>:int=X
cb:=class<computes>:
    Apply(X:int)<computes>:int=X
Main():void=
    P:=ca{}
    Q:=cb{}
    Rows:=array{P.Apply(7),P.Apply(7),Q.Apply(7),Q.Apply(7)}
    var Sum:int=0
    for(V:Rows):set Sum+=V
    Print("values {Rows.Length} {Sum}")
