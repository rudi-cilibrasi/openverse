# expect: requires convergence
Helper()<computes>:int=42
F:type{_()<computes>:int}=Helper
c:=class<computes>{Value:int=F()}
Main():void=Print("{c{}.Value}")
