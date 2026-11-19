# A task resumed by a Signal subscribes a function before that Signal has
# called the subscribed ones: does that same Signal call it? (Epic's API: a
# Signal reaches "the tasks already suspended in Await and the callbacks
# currently subscribed"; subscribers are invoked after the awaiters.)
# OpenVerse (#724) prints (the Signal resumes the awaiters, then calls the
# functions subscribed at that point, the new one too):
#   awaiter 1 | late 1 | after signal 1 | late 2 | after signal 2
# If the Signal called the functions subscribed when it began:
#   awaiter 1 | after signal 1 | late 2 | after signal 2
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM",
# 2026-11-19) prints awaiter 1 | late 1 | after signal 1 | late 2 | after signal 2,
# which OpenVerse printed without late 1 before; it now follows the VM.
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
