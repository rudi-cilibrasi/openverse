# (#515) programs --signal-no-rollback admits: each Signal outside every
# failure context, though near one (an if's branches, a for's body, also one
# the compiler moves into a continuation, a function called after the
# condition, a <decides> function that signals nothing, a task spawned by a
# function called in a condition, which signals later in its own task, a
# defer: that a return or a break out of a condition runs, which commits;
# and a for over choices in a defer: in a condition that signals nothing,
# both at a return and at the end of its block)
Two(N:int):int = N | N + 1
Note(E:event(int), N:int):int =
    E.Signal(N)
    N
Positive(N:int)<decides>:void = N > 0
Log(N:int):void = Print("heard {N}")
Shouter(E:event(int))<suspends>:void =
    Sleep(0.0)
    E.Signal(5)
Start(E:event(int)):int =
    spawn{Shouter(E)}
    1
Count(N:int):int =
    if (X := block{ defer{ R := for (A0 := (Two(0) | Two(2)), A1 := (Two(0) | Two(2)), A0 = 0) { Print("pair {A1}"); A1 } }; (if (N > 9) then return 0 else 3) }, X > 1) then 1 else 2
Pick(U:subscribable_event(int), N:int):int =
    defer:
        U.Signal(N)
    if (N > 0, (if (N > 1) then return N else 0) = 0):
        Print("normal")
    0
Main()<suspends>:void =
    E := event(int){}
    S := sticky_event(int){}
    U := subscribable_event(int){}
    C := U.Subscribe(Log)
    branch:
        loop:
            V := E.Await()
            Print("awaited {V}")
    Sleep(0.0)
    if (Positive[1]):
        E.Signal(1)
        U.Signal(1)
    else:
        S.Signal(0)
    Sleep(0.0)
    for (X := (Two(0) | Two(2)), Y := (Two(0) | Two(2)), X = 0):
        U.Signal(Y)
    if (Positive[2]) then Print("note {Note(E, 2)}")
    Sleep(0.0)
    S.Signal(3)
    Print("sticky {S.Await()}")
    C.Cancel()
    U.Signal(4)
    if (Start(E) > 0) then Print("started")
    Sleep(0.1)
    W := subscribable_event(int){}
    K := W.Subscribe(Log)
    Print("picked {Pick(W, 5)}")
    loop:
        block:
            defer:
                W.Signal(6)
            if ((if (1 > 0) then break else 0) = 0) then Print("no")
    K.Cancel()
    Print("count {Count(1)} {Count(10)}")
