# expect: requires convergence
Helper()<computes>:int=42
K:int=Helper()
c:=class<computes>{Value:int=K}
Main():void=Print("{c{}.Value}")
