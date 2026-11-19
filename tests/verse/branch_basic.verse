# branch runs its body as a task over the function's variables (#156), stopped (and its defers run)
# when the task that started it ends (#724): here Main, so the tickers go on after Work returns
Ticker(Name:string)<suspends>:void =
    defer:
        Print("{Name} ticker stopped")
    var I:int = 0
    loop:
        Sleep(1.0)
        set I += 1
        Print("{Name} tick {I}")
Work()<suspends>:int =
    var Count:int = 0
    branch:
        loop:
            Sleep(0.5)
            set Count += 1
    branch:
        Ticker("w")
    Sleep(2.2)
    Print("work done, count {Count}")
    Count
Main()<suspends>:void =
    R := Work()
    Print("got {R}")
    Sleep(2.0)
    Print("again")
    R2 := Work()
    Print("got {R2}")
    Sleep(1.0)
    Print("end")
