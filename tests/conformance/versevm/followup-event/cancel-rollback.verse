# A Cancel in a failure context that fails (the Book, ch. 14, "Transactional
# Behavior": "the subscription remains active"; Epic's API gives Cancel
# <transacts>). Is it undone, so that the next Signal still calls the
# function?
# OpenVerse (#724) prints:
#   rolled back | seen 1
# If the cancellation survives the failed condition:
#   rolled back | seen 0
counter := class:
    var Seen:int = 0
    Receive(N:int):void =
        set Seen = N

Main():void =
    E := event(int){}
    C := counter{}
    S := E.Subscribe(C.Receive)
    if (S.Cancel(), false?):
        Print("OVPROBE unexpected")
    else:
        Print("OVPROBE rolled back")
    E.Signal(1)
    Print("OVPROBE seen {C.Seen}")
    S.Cancel()
