# expect: a function type determining all its method type arguments
box(t:type):=class:
    V:t
    Same(X:u where u:type)<computes>:u=X
Main():void=
    F:type{_(:int)<computes>:rational}=box(string){V:="tag"}.Same
