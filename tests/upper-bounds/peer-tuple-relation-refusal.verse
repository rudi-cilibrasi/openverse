Upper(X:u where t:type,u:subtype(t))<computes>:t=X
Main():void=
    F:type{_(:int,:int)<computes>:int}=Upper
    Print("{F(1,2)}")
