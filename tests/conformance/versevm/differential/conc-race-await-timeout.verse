# A race between awaiting an event and a timeout: once the event is
# signalled in time, once it is not.
# Tests LANGUAGE.md, Concurrency: event(t) with Signal and Await, race; a
# race's loser (the timeout, or the await) is cancelled. The margins are
# 0.3 s or more.
# OpenVerse prints (Lean and C agree):
#   in time 7 | too late -1 | done
Later(E:event(int), D:float, V:int)<suspends>:void =
    Sleep(D)
    E.Signal(V)

Wait(E:event(int), Limit:float)<suspends>:int =
    race:
        E.Await()
        block:
            Sleep(Limit)
            -1

Main()<suspends>:void =
    E := event(int){}
    spawn{Later(E, 0.2, 7)}
    A := Wait(E, 0.6)
    Print("OVPROBE in time {A}")
    F := event(int){}
    spawn{Later(F, 0.9, 8)}
    B := Wait(F, 0.3)
    Print("OVPROBE too late {B}")
    Sleep(0.8)
    Print("OVPROBE done")
