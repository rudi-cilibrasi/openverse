# expect: the value of the constant K calls Helper, which might not complete
Helper()<computes>:int=42
K:int=Helper()
c:=class<computes>{Value:int=K}
Main():void=Print("{c{}.Value}")
