source(t:type):=interface:
    Get():t
    Pair(X:t)<computes>:tuple(t,int)=(X,7)
box(t:type,h:type):=class(source(t)):
    V:t
    Hidden:h
    Get<override>():t=V
    Bind()<computes>:type{_(:t)<computes>:tuple(t,rational)}=Pair
Bind(B:source(t) where t:type)<computes>:type{_(:t)<computes>:tuple(t,rational)}=B.Pair
Main():void=
    B:=box(string,int){V:="value",Hidden:=9}
    F:=Bind(B)
    G:=B.Bind()
    A:=F("first")
    Z:=G("second")
    Print("{A(0)} {Floor(A(1))} {Z(0)} {Floor(Z(1))}")
