# A task resumed by a Signal subscribes a function before that Signal has
# called the subscribed ones: does that same Signal call it? (Epic's API: a
# Signal reaches "the tasks already suspended in Await and the callbacks
# currently subscribed"; subscribers are invoked after the awaiters.)
# OpenVerse (#724) prints (the Signal calls the functions subscribed when it
# began; the new one is first called by the next Signal):
#   awaiter 1 | after signal 1 | late 2 | after signal 2
# If the Signal calls the functions subscribed when the awaiters are done:
#   awaiter 1 | late 1 | after signal 1 | late 2 | after signal 2
holder := class:
    var Sub:?cancelable = false

OnLate(N:int):void =
    Print("OVPROBE late {N}")

Waiter(E:event(int), H:holder)<suspends>:void =
    V := E.Await()
    Print("OVPROBE awaiter {V}")
    set H.Sub = option{E.Subscribe(OnLate)}

Main()<suspends>:void =
    E := event(int){}
    H := holder{}
    spawn{Waiter(E, H)}
    E.Signal(1)
    Print("OVPROBE after signal 1")
    Sleep(0.1)
    E.Signal(2)
    Print("OVPROBE after signal 2")
    if (S := H.Sub?) then S.Cancel()
