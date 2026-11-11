Same(X:t,Y:t where t:subtype(comparable))<computes><decides>:t=
    X=Y
    X
Bind(X:t where t:subtype(comparable))<computes>:type{_(:t,:t)<computes><decides>:t}=Same
Use(X:t,Y:t where t:subtype(comparable))<computes>:int=
    F:type{_(:t,:t)<computes><decides>:t}=Same
    if (F[X,Y]) then 1 else 0
Main():void=
    F:=Bind(3)
    if (V:=F[3,3]) then Print("same {V}")
    if (F[3,4]) then Print("wrong") else Print("different")
    Print("{Use("s","s")} {Use(array{1},array{2})}")
