# A method with an optional named parameter as a value of a type that
# omits it and widens its result (#503): its default at the call
box(t:type):=class:
    V:t
    Code(?X:int=7)<computes>:int=X
Main():void=
    F:type{_()<computes>:rational}=box(string){V:="tag"}.Code
    Print("{Floor(F())}")
