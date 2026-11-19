thing := class:
    N:int

MakeThing<constructor>(N:int) := thing:
    N := N

Main():void =
    if (T := MakeThing(1), T.N > 0):
        Print("OVPROBE constructor in condition")
    Print("OVPROBE after")
