# spawn and Await: the task's value, a task awaited twice (the second time
# after it has finished), and a task that finished before it was awaited.
# Tests LANGUAGE.md, Concurrency: "spawn with task(t) and Await"; the Book's
# API (task, Await): the result of a finished task.
# OpenVerse prints (Lean and C agree):
#   spawned | work 21 done | awaited 42 | again 42 quick 10
Work(N:int)<suspends>:int =
    Sleep(0.2)
    Print("OVPROBE work {N} done")
    N * 2

Quick(N:int)<suspends>:int =
    N + 1

Main()<suspends>:void =
    T := spawn{Work(21)}
    Q := spawn{Quick(9)}
    Print("OVPROBE spawned")
    V := T.Await()
    Print("OVPROBE awaited {V}")
    W := T.Await()
    X := Q.Await()
    Print("OVPROBE again {W} quick {X}")
