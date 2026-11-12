# expect: expected type
box(t:type):=class:
    V:t
    Code()<computes>:int=7
Main():void=
    F:=box(string){V:="tag"}.Code
    G:type{_()<computes>:rational}=F
