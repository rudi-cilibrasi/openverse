# A task resumed by a Signal cancels a subscription before that Signal has
# called the subscribed functions: does that same Signal still call it?
# (The Verse VM calls a function that a resumed awaiter subscribes in the
# same Signal, UEFN 43.12, subscribe-from-awaiter: it takes its list of
# functions after the awaiters went on.)
# OpenVerse (#724) prints (the awaiters go on first, then the Signal calls
# the functions still subscribed):
#   awaiter 1 | after signal 1 | after signal 2
# If the Signal took its list before resuming the awaiters:
#   awaiter 1 | handler 1 | after signal 1 | after signal 2
holder := class:
    var Sub:?cancelable = false

OnHandler(N:int):void =
    Print("OVPROBE handler {N}")

Waiter(E:event(int), H:holder)<suspends>:void =
    V := E.Await()
    Print("OVPROBE awaiter {V}")
    if (S := H.Sub?) then S.Cancel()

Main()<suspends>:void =
    E := event(int){}
    H := holder{}
    set H.Sub = option{E.Subscribe(OnHandler)}
    spawn{Waiter(E, H)}
    E.Signal(1)
    Print("OVPROBE after signal 1")
    Sleep(0.1)
    E.Signal(2)
    Print("OVPROBE after signal 2")
