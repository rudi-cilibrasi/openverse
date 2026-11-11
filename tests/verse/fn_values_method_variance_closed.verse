box(t:type):=class:
    V:t
    Get():t=V
Main():void=
    B:=box(int){V:=7}
    F:type{_():rational}=B.Get
    Print("{Floor(F())}")
