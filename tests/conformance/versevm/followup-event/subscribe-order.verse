# In what order does an event's Signal call the functions subscribed to it?
# Epic's API reference says "in a randomised order on every signal"; the
# Book's chapter 14 example lists them in subscription order. Three methods
# are subscribed, A then B then C, and the event is signalled three times.
# OpenVerse (#724) prints (subscription order, every time):
#   a 1 | b 1 | c 1 | a 2 | b 2 | c 2 | a 3 | b 3 | c 3 | after
# If the order is shuffled on each Signal, the letters within a round vary
# (and may vary from run to run).
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM",
# 2026-11-19) prints, in one run:
#   c 1 | b 1 | a 1 | c 2 | b 2 | a 2 | a 3 | b 3 | c 3 | after
# The order varies between Signals, as the API says. A documented
# difference: OpenVerse keeps subscription order; programs must not rely on
# the order.
tally := class:
    Name:string
    Note(N:int):void =
        Print("OVPROBE {Name} {N}")

Main():void =
    E := event(int){}
    A := tally{Name := "a"}
    B := tally{Name := "b"}
    C := tally{Name := "c"}
    SA := E.Subscribe(A.Note)
    SB := E.Subscribe(B.Note)
    SC := E.Subscribe(C.Note)
    E.Signal(1)
    E.Signal(2)
    E.Signal(3)
    Print("OVPROBE after")
    SA.Cancel()
    SB.Cancel()
    SC.Cancel()
