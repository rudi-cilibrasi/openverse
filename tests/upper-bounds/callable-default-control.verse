Apply(F:type{_(:int)<computes>:int},?X:int=F(7))<computes>:tuple(type{_(:int)<computes>:int},int)=(F,X)
Twice(X:int)<computes>:int=X+X
Main():void=
    F:type{_(:int)<computes>:int}=Twice
    R:=Apply(F)
    Print("default {R(1)} again {R(0)(3)}")
