box(t:type):=class:
    V:t
    Empty(P:tuple())<computes>:int=7
    Code()<computes>:int=9
Bind(B:box(t) where t:type)<computes>:tuple(type{_()<computes>:rational},type{_(:tuple())<computes>:rational})=(B.Empty,B.Code)
Main():void=
    R:=Bind(box(string){V:="tag"})
    F:=R(0)
    G:=R(1)
    Print("{Floor(F())} {Floor(G(()))}")
