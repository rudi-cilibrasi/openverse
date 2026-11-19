# A subscribed function that signals the same event again: does the inner
# Signal call the functions at once (depth first), before the outer call
# goes on, or later?
# OpenVerse (#724) prints (depth first):
#   in 1 | in 2 | in 3 | out 3 | out 2 | out 1 | after
# If a Signal made inside a subscribed function were deferred:
#   in 1 | out 1 | in 2 | out 2 | in 3 | out 3 | after
relay := class:
    E:event(int)
    OnRelay(N:int):void =
        Print("OVPROBE in {N}")
        if (N < 3):
            E.Signal(N + 1)
        Print("OVPROBE out {N}")

Main():void =
    E := event(int){}
    R := relay{E := E}
    S := E.Subscribe(R.OnRelay)
    E.Signal(1)
    Print("OVPROBE after")
    S.Cancel()
