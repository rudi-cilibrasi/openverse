# A task's end resumes its awaiters in the order they registered, each until
# it waits again or ends before the next (the Book's API, task, Await:
# "Multiple awaiters are allowed and are resumed in the order they
# registered"; Coroutines/SpawnAndTask.versetest:292-321, TestAwait3,
# translated: Sleep(0.04) is two ticks, Sleep(0.01) one). Arms A and C of
# one sync register as it starts, B a tick later: when the task ends, A2,
# then C2 (whose arm then waits a tick), then B3, not the arms' order.
Y2Z()<suspends>:void =
    Print("Y")
    Sleep(0.04)
    Print("Z")
Main()<suspends>:void =
    Print("a")
    T := spawn{Y2Z()}
    Print("b")
    sync:
        block:
            Print("A1")
            T.Await()
            Print("A2")
        block:
            Print("B1")
            Sleep(0.01)
            Print("B2")
            T.Await()
            Print("B3")
        block:
            Print("C1")
            T.Await()
            Print("C2")
            Sleep(0.01)
            Print("C3")
    Print("c")
