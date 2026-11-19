# A subscription cancelled by another subscribed function while a Signal is
# calling them: is the cancelled function still called by that Signal?
# A cancels B's subscription; B prints whether A had cancelled it already,
# so the answer does not depend on the order the two are called in.
# OpenVerse (#724) prints (calls in subscription order, A first; a function
# cancelled before its turn is skipped):
#   a 1 | a 2 | after
# If the Signal still calls B after A cancelled it:
#   a 1 | b 1 after cancel | a 2 | after
# If B was called before A (a shuffled order), the first round shows
#   b 1 before cancel | a 1, and the second round only a 2.
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM",
# 2026-11-19) prints the same: a 1 | a 2 | after.
canceller := class:
    var Victim:?cancelable = false
    var Done:logic = false
    OnA(N:int):void =
        Print("OVPROBE a {N}")
        if (V := Victim?, not Done?):
            set Done = true
            V.Cancel()
    OnB(N:int):void =
        if (Done?) then Print("OVPROBE b {N} after cancel") else Print("OVPROBE b {N} before cancel")

Main():void =
    E := event(int){}
    K := canceller{}
    SA := E.Subscribe(K.OnA)
    SB := E.Subscribe(K.OnB)
    set K.Victim = option{SB}
    E.Signal(1)
    E.Signal(2)
    Print("OVPROBE after")
    SA.Cancel()
