Id(X:t where t:type)<computes>:t=X
Twice(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)|F(X)
Values(X:t where t:type)<computes>:[]t=for{Twice(Id,X)}
Main():void=
    A:=Values(7)
    B:=Values("s")
    Print("{A.Length} {B.Length}")
    for(X:A):Print("{X}")
    for(X:B):Print(X)
