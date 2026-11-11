# A late error must remain untaken after the first body fails; the source handler rolls back.
counter := class:
    var N:int = 0
Two(N:int):int = N | N + 1
Lazy(C:counter, N:int)<transacts><decides>:int =
    N >= 0
    set C.N += 1
    N | Lazy[C, N - 1]
Even(C:counter, N:int)<transacts><decides>:int =
    N >= 0
    set C.N += 1
    N | Odd[C, N - 1]
Odd(C:counter, N:int)<transacts><decides>:int =
    N >= 0
    set C.N += 1
    N | Even[C, N - 1]
Stop(H:counter, N:int)<transacts><decides>:int =
    set H.N += 1
    Print("stop {N} state {H.N}")
    if (N > 0) then Stop[H, N - 1] else (false?; 0)
Main():void =
    C := counter{}
    var Total:int = 0
    if (R := for (A := (Two(0) | Two(2)), X := 1..2, L := Lazy[C, 0], B := (Two(0) | Two(2)), D := (Two(0) | Two(2))):
            set Total += 1
            Print("rolled back {Total}")
            if (X = 1) then (false?; 0) else Err()):
        Print("unexpected {R.Length}")
    else:
        Print("caught total {Total} visits {C.N}")
