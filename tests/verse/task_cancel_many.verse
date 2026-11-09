# many tasks cancelled one after another, each unwinding its defer: a task's
# root is unwound after the condition that reads it, not in it (#270), so the
# reference interpreter does not copy the heap at each cancel
Work(N:int)<suspends>:void =
    defer:
        if (Mod[N, 100] = 0):
            Print("unwound {N}")
    Sleep(10.0)
Main()<suspends>:void =
    var Ts:[]task(void) = array{}
    for (I := 0..299):
        set Ts += array{spawn{Work(I)}}
    Sleep(1.0)
    for (T : Ts):
        T.Cancel()
    for (T : Ts):
        T.Cancel()
    Print("all cancelled")
