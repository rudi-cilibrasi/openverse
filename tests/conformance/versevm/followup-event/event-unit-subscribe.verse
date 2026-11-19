# Subscribe on an event without a value, event() (Epic's API: event(tuple())),
# with a function that takes none: is it admitted, and called by Signal()?
# OpenVerse (#724) prints:
#   ping | after first | after second
# (the second Signal comes after Cancel, so it calls nothing). A refusal
# (the function's type not fitting (:tuple()):void) answers it too.
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
