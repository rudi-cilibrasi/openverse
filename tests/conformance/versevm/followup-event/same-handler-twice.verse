# One function subscribed twice to one event: is it called twice by a
# Signal, and does cancelling one subscription leave the other?
# OpenVerse (#724) prints (each subscription is its own):
#   twice 1 | twice 1 | twice 2 | after
# If the second Subscribe of the same function were merged with the first:
#   twice 1 | after   (or twice 1 | twice 2 | after)
OnTwice(N:int):void =
    Print("OVPROBE twice {N}")

Main():void =
    E := event(int){}
    S1 := E.Subscribe(OnTwice)
    S2 := E.Subscribe(OnTwice)
    E.Signal(1)
    S1.Cancel()
    E.Signal(2)
    S2.Cancel()
    E.Signal(3)
    Print("OVPROBE after")
