# many tasks awaiting one event, a generic suspends function: each waiter's
# child frame is resumed after a test of its class, outside any condition,
# so a resumption does not make the reference interpreter copy the heap
# (#256); a generic suspends function that calls itself at bigger types
# runs the same way
Waiter(E:event(int), N:int)<suspends>:int =
    V := E.Await()
    V + N
Grow(X:t, N:int where t:type)<suspends>:int =
    Sleep(0.0)
    if (N > 0) then Grow(array{X}, N - 1) else 0
Main()<suspends>:void =
    E := event(int){}
    var Ts:[]task(int) = array{}
    for (I := 1..3000):
        set Ts += array{spawn{Waiter(E, I)}}
    Sleep(1.0)
    E.Signal(1)
    Sleep(1.0)
    var Sum:int = 0
    for (T : Ts):
        set Sum += T.Await()
    Print("{Sum} {Grow(1, 8)}")
