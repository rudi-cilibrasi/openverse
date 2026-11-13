holder(t:type,u:subtype(t)):=class<computes>:
    Value:u
    Up()<computes>:t=Value
Worker(F:type{_()<computes>:rational})<suspends>:void=
    defer:
        if(F()=7):Print("cleanup 7")
    Sleep(10.0)
    Print("bad")
Main()<suspends>:void=
    H:=holder(rational,int){Value:=7}
    F:type{_()<computes>:rational}=H.Up
    race:
        Worker(F)
        block:
            Sleep(0.0)
            Print("winner")
    Print("after")
