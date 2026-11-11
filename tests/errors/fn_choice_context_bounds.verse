# expect: 'Same' is generic
Same(X:t where t:subtype(comparable))<computes>:t=X
Twice(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)|F(X)
Run(X:t where t:type)<computes>:[]t=for{Twice(Same,X)}
Main():void={}
