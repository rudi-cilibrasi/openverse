Apply(F:t,X:int where t:subtype(type{_(:int)<computes>:int}))<computes>:tuple(t,int)=(F,F(X))
Twice(X:int)<computes>:int=X+X
Main():void=
    F:type{_(:int)<computes>:int}=Twice
    R:=Apply(F,7)
    Print("callable {R(1)} again {R(0)(3)}")
