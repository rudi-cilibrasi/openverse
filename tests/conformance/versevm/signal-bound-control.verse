relay := class:
    E:event(int)

    Send(N:int):void =
        E.Signal(N)

Main():void =
    R := relay{E := event(int){}}
    Send := R.Send
    Send(1)
    Print("OVPROBE after")
