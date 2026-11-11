base(t:type):=class:
    V:t
    Code(X:rational)<computes>:int=Floor(X)
child(t:type):=class(base(t)):
    Code(X:string)<computes>:int=X.Length
Bind(B:base(t) where t:type)<computes>:type{_(:int)<computes>:rational}=B.Code
Main():void=
    F:=Bind(child(string){V:="tag"})
    Print("{Floor(F(7))}")
