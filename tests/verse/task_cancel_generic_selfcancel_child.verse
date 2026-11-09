# generic: a task of a generic function cancels itself and spawns a child;
# another, resumed, is cancelled by its child's first run. Expected:
# still running s / S defer s / P after spawn i / P defer i / C end s /
# Kid end i / end
C(X:t, N:string where t:type)<suspends>:t =
    Sleep(0.5)
    Print("C end {N}")
    X
Kid(P:task(t), X:t, N:string where t:type)<suspends>:t =
    P.Cancel()
    Sleep(0.6)
    Print("Kid end {N}")
    X
S(Me:event(task(t)), X:t, N:string where t:type)<suspends>:t =
    defer:
        Print("S defer {N}")
    T := Me.Await()
    T.Cancel()
    spawn{C(X, N)}
    Print("still running {N}")
    Sleep(1.0)
    Print("never")
    X
P(Me:event(task(t)), X:t, N:string where t:type)<suspends>:t =
    defer:
        Print("P defer {N}")
    T := Me.Await()
    spawn{Kid(T, X, N)}
    Print("P after spawn {N}")
    Sleep(1.0)
    Print("never")
    X
Main()<suspends>:void =
    E1 := event(task(string)){}
    T1 := spawn{S(E1, "x", "s")}
    E2 := event(task(int)){}
    T2 := spawn{P(E2, 1, "i")}
    E1.Signal(T1)
    E2.Signal(T2)
    Sleep(2.0)
    Print("end")
