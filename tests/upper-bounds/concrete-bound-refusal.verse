base:=class<computes><concrete>{Power:int=1}
F(X:t where t:concrete_subtype(base))<computes>:int=X.Power
Main():void=Print("{F(base{})}")
