# A Subscribe in a failure context that fails (the Book, ch. 14,
# "Transactional Behavior": "the subscription never takes effect"; Epic's
# API gives Subscribe <transacts>). Is it undone, so that the next Signal
# does not call the function?
# OpenVerse (#724) prints:
#   rolled back | seen 0
# If the subscription survives the failed condition:
#   rolled back | seen 1
# A refusal (the compiler not admitting Subscribe in a failure context)
# answers it too.
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM",
# 2026-11-19) prints the same.
counter := class:
    var Seen:int = 0
    Receive(N:int):void =
        set Seen = N

Main():void =
    E := event(int){}
    C := counter{}
    if (S := E.Subscribe(C.Receive), false?):
        Print("OVPROBE unexpected")
    else:
        Print("OVPROBE rolled back")
    E.Signal(1)
    Print("OVPROBE seen {C.Seen}")
