box(t:type):=class:
    V:t
    Add(P:tuple(rational,rational))<computes>:rational=Floor(P(0))+Floor(P(1))
Bind(B:box(t) where t:type)<computes>:type{_(:int,:int)<computes>:rational}=B.Add
Main():void=
    F:=Bind(box(string){V:="tag"})
    Print("{Floor(F(3,4))}")
