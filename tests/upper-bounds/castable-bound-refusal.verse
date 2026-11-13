plain:=class<computes>{Power:int=1}
F(X:t where t:castable_subtype(plain))<computes>:int=X.Power
Main():void=Print("{F(plain{})}")
