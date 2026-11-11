Same(X:t,Y:t where t:subtype(comparable))<decides>:t=
    X=Y
    X
token:=class<unique>:
    N:int
point:=struct:
    X:int
    Y:int
Main():void=
    F:type{_(:token,:token)<decides>:token}=Same
    P:type{_(:point,:point)<decides>:point}=Same
    A:=token{N:=3}
    B:=token{N:=3}
    if(R:=F[A,A])then Print("same {R.N}")else Print("wrong")
    if(F[A,B])then Print("wrong")else Print("different")
    if(R:=P[point{X:=1,Y:=2},point{X:=1,Y:=2}])then Print("point {R.X} {R.Y}")
