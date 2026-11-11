box(t:type):=class:
    V:t
    Echo(P:tuple(rational))<computes>:int=Floor(P(0))
Bind(B:box(t) where t:type)<computes>:type{_(:int)<computes>:rational}=B.Echo
Main():void=
    F:=Bind(box(string){V:="tag"})
    Print("{Floor(F(7))}")
