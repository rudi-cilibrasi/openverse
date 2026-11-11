# expect: expected type
box(t:type):=class:
    V:t
    Take(X:rational)<computes>:rational=X
Main():void=
    F:type{_(:int)<computes>:int}=box(string){V:="tag"}.Take
