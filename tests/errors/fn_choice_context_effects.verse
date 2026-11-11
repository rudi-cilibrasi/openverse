# expect: 'Id' is generic
Id(X:t where t:type):t=X
Twice(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)|F(X)
Main():void=
    R:=for{Twice(Id,7)}
