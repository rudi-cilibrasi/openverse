# A Signal with no awaiter is lost: a task that starts awaiting afterwards
# gets the next Signal's value.
# Tests LANGUAGE.md, Readings, "Event waiter resumption": "an await made
# meanwhile joins the next Signal"; the Book's API: event is not sticky.
# OpenVerse prints (Lean and C agree):
#   got 2 | done
Waiter(E:event(int))<suspends>:void =
    V := E.Await()
    Print("OVPROBE got {V}")

Main()<suspends>:void =
    E := event(int){}
    E.Signal(1)
    spawn{Waiter(E)}
    Sleep(0.1)
    E.Signal(2)
    E.Signal(3)
    Sleep(0.1)
    Print("OVPROBE done")
