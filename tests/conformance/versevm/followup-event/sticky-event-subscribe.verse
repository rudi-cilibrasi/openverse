# Subscribe on a sticky_event (Epic's API: sticky_event(t) is a class of
# event(t)) that was signalled before the subscription: is the function
# called at once with the kept value, and by later Signals?
# OpenVerse (#724) prints (a sticky_event has event's Subscribe; Subscribe
# calls nothing, only later Signals do):
#   subscribed | sticky 2 | after
# If Subscribe replays the kept value:
#   sticky 1 | subscribed | sticky 2 | after
# A refusal answers whether 43.12's sticky_event has Subscribe.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM",
# 2026-11-19) refuses it: 3506 "Unknown identifier `sticky_event`"
# ("Did you forget to specify using { /Verse.org/Restricted }"). A program
# cannot name sticky_event on 43.12, so this cannot run there as user code.
OnSticky(N:int):void =
    Print("OVPROBE sticky {N}")

Main():void =
    E := sticky_event(int){}
    E.Signal(1)
    S := E.Subscribe(OnSticky)
    Print("OVPROBE subscribed")
    E.Signal(2)
    Print("OVPROBE after")
    S.Cancel()
