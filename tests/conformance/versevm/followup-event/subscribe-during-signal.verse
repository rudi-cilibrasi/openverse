# A function subscribed by another one while a Signal is calling them: does
# that same Signal call it? (Epic's API: a Signal reaches "the callbacks
# currently subscribed".)
# OpenVerse (#724) prints (it is first called by the next Signal):
#   first 1 | first 2 | added 2 | after
# If the Signal that is running calls it too:
#   first 1 | added 1 | first 2 | added 2 | after
adder := class:
    E:event(int)
    var Extra:?cancelable = false
    OnFirst(N:int):void =
        Print("OVPROBE first {N}")
        if (not Extra?):
            set Extra = option{E.Subscribe(OnAdded)}
    OnAdded(N:int):void =
        Print("OVPROBE added {N}")

Main():void =
    E := event(int){}
    D := adder{E := E}
    S := E.Subscribe(D.OnFirst)
    E.Signal(1)
    E.Signal(2)
    Print("OVPROBE after")
    S.Cancel()
    if (X := D.Extra?) then X.Cancel()
