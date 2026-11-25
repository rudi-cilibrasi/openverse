# expect: the default of field 'Value' of c calls a.Get, which might not complete
a:=class<computes>{Get()<computes>:int=42}
c:=class<computes>{Value:int=a{}.Get()}
Main():void=Print("{c{}.Value}")
