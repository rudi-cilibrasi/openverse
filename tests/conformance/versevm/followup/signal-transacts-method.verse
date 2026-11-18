relay := class:
    E:event(int)

    Send(N:int)<transacts>:void =
        E.Signal(N)

Main():void =
    R := relay{E := event(int){}}
    R.Send(1)
    Print("OVPROBE after")
