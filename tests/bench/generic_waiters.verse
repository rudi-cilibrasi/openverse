# 4000 tasks spawned from generic code, each awaiting one event through a
# generic suspends call (#256): the reference interpreter resumes each one
# outside any condition, so the run is linear in the number of tasks.
Wait(E:event(int), X:t where t:type)<suspends>:int = E.Await()
Go(E:event(int), X:t, N:int where t:type)<suspends>:void =
    for (I := 0..N-1):
        spawn{Wait(E, X)}
    Sleep(1.0)
Main()<suspends>:void =
    E := event(int){}
    Go(E, 1, 4000)
    E.Signal(7)
    Sleep(1.0)
    Print("done")
