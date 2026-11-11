Id(X:t where t:type)<computes>:t=X
Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)
Use(X:t where t:type)<computes>:t=
    F:type{_(:t)<computes>:t}=Id
    G:type{_(:type{_(:t)<computes>:t},:t)<computes>:t}=Apply
    G(F,X)
Main():void=Print("{Use(7)} {Use("hello")}")
