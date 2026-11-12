# Each individual duration is supported; accumulated ticks overflow int64.
Main()<suspends>:void=
    Print("before")
    var I:int=0
    loop:
        if(I=400):break
        Sleep(999999999999999.0)
        set I+=1
    Print("after")
