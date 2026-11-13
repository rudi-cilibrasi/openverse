Apply(F:type{_(:int)<computes><decides>:int},X:int)<computes><decides>:int=F[X]
Positive(X:int)<computes><decides>:int=
    X>0
    X
Main():void=
    F:type{_(:int)<computes><decides>:int}=Positive
    if(V:=Apply[F,3])then Print("value {V}")else Print("bad")
    if(Apply[F,-1])then Print("bad")else Print("failure")
