# One event both awaited by a task and subscribed to: in which order do the
# awaiter and the subscribed function run, and does either run after the
# Signal returns? (Epic's API: "Subscribers ... are invoked only after every
# waiting task has been resumed"; awaiters resume in the order they
# suspended, each until it blocks.)
# OpenVerse (#724) prints (the awaiter goes on inside Signal, then the
# function is called, both before Signal returns):
#   awaiter 1 | handler 1 | after signal | after wait
# If the function were called first:
#   handler 1 | awaiter 1 | after signal | after wait
# If the awaiter only resumed after the Signal returned:
#   handler 1 | after signal | awaiter 1 | after wait
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM",
# 2026-11-19) prints the same.
OnHandler(N:int):void =
    Print("OVPROBE handler {N}")

Waiter(E:event(int))<suspends>:void =
    V := E.Await()
    Print("OVPROBE awaiter {V}")

Main()<suspends>:void =
    E := event(int){}
    S := E.Subscribe(OnHandler)
    spawn{Waiter(E)}
    E.Signal(1)
    Print("OVPROBE after signal")
    Sleep(0.1)
    Print("OVPROBE after wait")
    S.Cancel()
