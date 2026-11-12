box(t:type):=class:
    V:t
    Code()<computes>:int=7
Bind(B:box(t) where t:type)<computes>:type{_()<reads><decides>:rational}=B.Code
Main():void=
    F:=Bind(box(string){V:="tag"})
    if(R:=F[])then Print("{Floor(R)}")else Print("wrong")
