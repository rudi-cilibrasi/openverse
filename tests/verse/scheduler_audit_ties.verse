Main()<suspends>:void=
    Winner:=race:
        block:
            defer:Print("left cleanup")
            Sleep(0.01)
            Print("left completed")
            1
        block:
            defer:Print("right cleanup")
            Sleep(0.01)
            Print("wrong right completed")
            2
    Print("winner {Winner}")
    Immediate:=race:
        block:
            Print("first started")
            Sleep(-1.0)
            11
        block:
            Print("wrong second started")
            Sleep(0.01)
            22
    Print("immediate {Immediate}")
