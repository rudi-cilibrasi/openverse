box(t:type):=class:
    V:t
    Add(X:rational,Y:rational)<computes>:rational=Floor(X)+Floor(Y)
Bind(B:box(t) where t:type)<computes>:type{_(:tuple(int,int))<computes>:rational}=B.Add
Main():void=
    F:=Bind(box(string){V:="tag"})
    Print("{Floor(F((3,4)))}")
