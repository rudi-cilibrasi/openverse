# a loop of suspending calls reuses one frame per call site (#156)
Step(I:int)<suspends>:int =
    Sleep(0.0)
    I + 1
Main()<suspends>:void =
    var I:int = 0
    var Sum:int = 0
    loop:
        if (I >= 20000) then break
        set I = Step(I)
        set Sum += I
    Print("{I} {Sum}")
