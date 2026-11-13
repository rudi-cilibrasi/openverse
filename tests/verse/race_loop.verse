# a loop of races reuses the arms' frames (#156)
Main()<suspends>:void =
    var Wins:int = 0
    var I:int = 0
    loop:
        if (I >= 2000) then break
        set I += 1
        W := race:
            block:
                Sleep(0.01)
                1
            block:
                Sleep(1.0)
                0
        set Wins += W
    Print("{Wins}")
