base:=class<computes>{Power:int=1}
fine:=class<computes><castable>(base){}
F(X:t where t:castable_subtype(base))<computes>:int=X.Power
G(X:t where t:subtype(base))<computes>:int=F(X)
Main():void=Print("{G(fine{})}")
