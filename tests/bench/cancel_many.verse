# 4,000 tasks cancelled one after another (#270): each root is unwound after
# the condition that reads it, so the reference interpreter copies no heap
Work(N:int)<suspends>:void =
    defer:
        if (N = 0):
            Print("unwound {N}")
    Sleep(10.0)
Main()<suspends>:void =
    var Ts:[]task(void) = array{}
    for (I := 0..3999):
        set Ts += array{spawn{Work(I)}}
    Sleep(1.0)
    for (T : Ts):
        T.Cancel()
    Print("all cancelled")
