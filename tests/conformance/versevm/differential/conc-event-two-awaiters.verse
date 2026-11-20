# Two tasks await one event: in which order a Signal resumes them, and
# whether they run before the code after the Signal.
# Tests LANGUAGE.md, Readings, "Event waiter resumption": "inside Signal, in
# the order they suspended, each until it waits again or ends" (Epic agrees
# for one awaiter: followup-event/await-and-subscribe). Last-in-first-out
# would print b before a.
# OpenVerse prints (Lean and C agree):
#   a got 5 | b got 5 | after signal | after wait
Waiter(E:event(int), Name:string)<suspends>:void =
    V := E.Await()
    Print("OVPROBE {Name} got {V}")

Main()<suspends>:void =
    E := event(int){}
    spawn{Waiter(E, "a")}
    spawn{Waiter(E, "b")}
    Sleep(0.1)
    E.Signal(5)
    Print("OVPROBE after signal")
    Sleep(0.1)
    Print("OVPROBE after wait")
