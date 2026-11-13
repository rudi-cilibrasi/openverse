car:=class<computes>{Name:string="precise"}
KeepZero(X:t where t:subtype(tuple()))<computes>:t=X
Main():void=Print(KeepZero(car{}).Name)
