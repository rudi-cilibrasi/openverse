# expect: the default of field 'Value' of c calls a value of type type{_()<computes>:int}, which might not complete
Helper()<computes>:int=42
F:type{_()<computes>:int}=Helper
c:=class<computes>{Value:int=F()}
Main():void=Print("{c{}.Value}")
