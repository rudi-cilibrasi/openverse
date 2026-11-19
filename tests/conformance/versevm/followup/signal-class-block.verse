loud := class:
    E:event(int)
    block:
        E.Signal(1)

Main():void =
    L := loud{E := event(int){}}
    Print("OVPROBE built")
