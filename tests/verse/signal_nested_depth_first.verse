# A Signal made by an awaiter runs its own awaiters before it returns: depth
# first (the Book's tests, FORT-1126351_cross_event_reentrancy_probe): y1,
# resumed inside r1's Signal, goes on before x2, the next of X's round
Relay(Name:string, From:event(int), To:event(int))<suspends>:void =
    V := From.Await()
    Print("{Name} got {V}, signals")
    To.Signal(V + 1)
    Print("{Name} after its signal")
Leaf(Name:string, E:event(int))<suspends>:void =
    V := E.Await()
    Print("{Name} got {V}")
Main()<suspends>:void =
    X := event(int){}
    Y := event(int){}
    spawn{Relay("r1", X, Y)}
    spawn{Leaf("x2", X)}
    spawn{Leaf("y1", Y)}
    X.Signal(1)
    Print("main after signal")
