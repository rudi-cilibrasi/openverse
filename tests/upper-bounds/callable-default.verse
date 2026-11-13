Apply(F:t,?X:int=F(7) where t:subtype(type{_(:int)<computes>:int}))<computes>:tuple(t,int)=(F,X)
Twice(X:int)<computes>:int=X+X
Main():void=
    F:type{_(:int)<computes>:int}=Twice
    R:=Apply(F)
    Print("default {R(1)} again {R(0)(3)}")
