# rush: the first arm to end gives the value; the others go on as tasks until the function exits (#156)
Step(Name:string, N:int, D:float)<suspends>:string =
    defer:
        Print("{Name} unwound")
    var I:int = 0
    loop:
        if (I >= N) then break
        Sleep(D)
        set I += 1
        Print("{Name} step {I}")
    Name
Leader()<suspends>:void =
    W := rush:
        Step("fast", 2, 0.5)
        Step("slow", 4, 0.75)
    Print("winner {W}")
    Sleep(1.0)
    Print("leader exits")
Main()<suspends>:void =
    Leader()
    Sleep(2.0)
    Print("end")
