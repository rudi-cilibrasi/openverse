# expect: the default of field 'Value' of c calls Helper, which might not complete
Helper()<computes>:int=42
c:=class<computes>{Value:int=Helper()}
Main():void={}
