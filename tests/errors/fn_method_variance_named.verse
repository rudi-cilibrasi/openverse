# expect: a method with named parameters is not a value
box(t:type):=class:
    V:t
    Code(?X:int=7)<computes>:int=X
Main():void=
    F:type{_()<computes>:rational}=box(string){V:="tag"}.Code
