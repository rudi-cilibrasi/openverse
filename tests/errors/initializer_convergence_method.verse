# expect: requires convergence
a:=class<computes>{Get()<computes>:int=42}
c:=class<computes>{Value:int=a{}.Get()}
Main():void=Print("{c{}.Value}")
