# Subscribe on an event without a value, event() (Epic's API: event(tuple())),
# with a function that takes none: is it admitted, and called by Signal()?
# OpenVerse (#724) prints:
#   ping | after first | after second
# (the second Signal comes after Cancel, so it calls nothing). A refusal
# (the function's type not fitting (:tuple()):void) answers it too.
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM",
# 2026-11-19) admits it and prints the same.
OnPing():void =
    Print("OVPROBE ping")

Main():void =
    E := event(){}
    S := E.Subscribe(OnPing)
    E.Signal()
    Print("OVPROBE after first")
    S.Cancel()
    E.Signal()
    Print("OVPROBE after second")
