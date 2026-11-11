# expect: expected type
box(t:type):=class:
    V:t
    Take(X:int)<computes>:int=X
Main():void=
    F:type{_(:rational)<computes>:rational}=box(string){V:="tag"}.Take
