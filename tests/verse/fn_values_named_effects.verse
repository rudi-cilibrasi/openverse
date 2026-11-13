# Effects through function values of functions with named parameters
# (#503): failure rolls back the call, its defaults included; a <suspends>
# value waits, also spawned with a named argument; a <decides> value runs
# once per alternative tried in failure and choice contexts.
cell := class:
    var N:int = 0
Bump(C:cell, ?By:int = 1)<transacts>:int =
    set C.N += By
    C.N
Try(C:cell, X:int, ?Before:int = Bump(C), ?Max:int = 3)<transacts><decides>:int =
    set C.N += X
    X <= Max
    C.N
Later(C:cell, ?Ticks:int = 1)<suspends>:void =
    Sleep(0.0)
    set C.N += Ticks
    Print("later {C.N}")
Check(X:int, ?Limit:int = 3)<decides><computes>:int =
    X < Limit
    X
Main()<suspends>:void =
    C := cell{}
    F:type{_(:cell, :int)<transacts><decides>:int} = Try
    if (V := F[C, 2]) then Print("ok {V}")
    if (V := F[C, 5]) then Print("bad") else Print("rolled back {C.N}")
    G:type{_(:cell, :int, ?Max:int)<transacts><decides>:int} = Try
    if (V := G[C, 5, ?Max := 9]) then Print("ok {V}")
    W:type{_(:cell)<suspends>:void} = Later
    W(C)
    WT:type{_(:cell, ?Ticks:int)<suspends>:void} = Later
    T := spawn{WT(C, ?Ticks := 10)}
    T.Await()
    Print("after {C.N}")
    K:type{_(:int)<decides><computes>:int} = Check
    KL:type{_(:int, ?Limit:int)<decides><computes>:int} = Check
    Xs := for (X := 1..5, V := K[X]) { V }
    Ys := for (X := 1..5, V := KL[X, ?Limit := 5]) { V }
    Print("{Xs.Length} {Ys.Length}")
    if (V := (K[7] | KL[9, ?Limit := 10])) then Print("first {V}")
