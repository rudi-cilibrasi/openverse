# Each duration is supported; accumulated checked-int ticks deliberately overflow.
Main()<suspends>:void=
    Print("before")
    var I:int=0
    loop:
        if(I=400):break
        Sleep(999999999999999.0)
        set I+=1
    Print("after")
