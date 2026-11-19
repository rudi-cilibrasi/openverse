# Cancelling one subscription twice (Epic's API: Cancel is "idempotent by
# convention", "cancelling twice ... does nothing"), and the event signalled
# afterwards.
# OpenVerse (#724) prints:
#   seen 1 | cancelled twice | seen 1
# A runtime error at the second Cancel would end the probe after "seen 1".
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM",
# 2026-11-19) prints the same.
counter := class:
    var Seen:int = 0
    Receive(N:int):void =
        set Seen = N

Main():void =
    E := event(int){}
    C := counter{}
    S := E.Subscribe(C.Receive)
    E.Signal(1)
    Print("OVPROBE seen {C.Seen}")
    S.Cancel()
    S.Cancel()
    Print("OVPROBE cancelled twice")
    E.Signal(2)
    Print("OVPROBE seen {C.Seen}")
