box(t:type):=class:
    Code()<computes>:int=7
holder(t:type):=class:
    F:type{_()<computes>:rational}=box(t){}.Code
Call(B:box(t),?F:type{_()<computes>:rational}=B.Code where t:type)<computes>:rational=F()
Bind(B:box(t) where t:type):type{_()<computes>:rational}=
    if(true?):
        B.Code
    else:
        B.Code
Main():void=
    B:=box(string){}
    H:=holder(string){}
    F:=Bind(B)
    Print("{Floor(H.F())} {Floor(Call(B))} {Floor(F())}")
