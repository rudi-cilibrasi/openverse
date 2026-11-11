wrap(t:type):=struct{V:t}
box(t:type,h:subtype(comparable)):=class:
    Hidden:h
    Pair(X:t)<computes>:tuple(t,int)=(X,7)
Bind(B:box([]wrap(t),u) where t:type,u:subtype(comparable))<computes>:type{_(:[]wrap(t))<computes>:tuple([]wrap(t),rational)}=B.Pair
Main():void=
    F:=Bind(box([]wrap(string),int){Hidden:=3})
    R:=F(array{wrap(string){V:="nested"}})
    Print("{R(0).Length} {Floor(R(1))}")
