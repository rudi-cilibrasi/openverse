# expect: the default of field 'Value' of c calls Helper, which might not complete
Helper(X:t where t:type)<computes>:t=X
c(t:type):=class<computes>{Value:[]t=Helper(array{})}
Main():void=Print("{c(int){}.Value.Length}")
