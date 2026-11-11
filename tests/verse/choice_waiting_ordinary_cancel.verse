Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return 0
    N|N+1
Run()<suspends>:void=
    var Total:int=0
    defer:Print("source cleanup {Total}")
    for(A:=(Two(1)|Two(3)),set Total+=A,B:=Early(10)):
        defer:
            set Total+=100
            Print("body cleanup {Total}")
        set Total+=B
        Print("waiting {A} {B} {Total}")
        Sleep(1.0)
        Print("unexpected")
Main()<suspends>:void=
    race:
        Run()
        block:
            Sleep(0.1)
            Print("winner")
