# expect: expected type
box(t:type):=class:
    V:t
    Code()<suspends>:int=block{Sleep(0.0);7}
Main():void=
    F:type{_():rational}=box(string){V:="tag"}.Code
