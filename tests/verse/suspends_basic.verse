# <suspends> functions, Sleep, and calls between them (#156)
Wait(N:int)<suspends>:int =
    Sleep(1.0)
    N * 2
Main()<suspends>:void =
    Print("start")
    Sleep(0.5)
    Print("after sleep")
    var Total:int = 0
    for (I := 1..3):
        X := Wait(I)
        set Total += X
        Print("got {X}")
    Print("total {Total} {Wait(10) + Wait(20)}")
