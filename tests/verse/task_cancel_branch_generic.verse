# branches in a generic function (at two types) that await a cancelled task
# in their first runs: each branch is cancelled, its function goes on.
# Expected: b1 defer int / b2 defer / G end / G defer / 7 / b1 defer ... 
W()<suspends>:int =
    Sleep(9.0)
    1
G(X:t, N:string where t:type)<suspends>:t =
    defer:
        Print("G defer {N}")
    T := spawn{W()}
    T.Cancel()
    branch:
        defer:
            Print("b1 defer {N}")
        T.Await()
        Print("never")
    branch:
        defer:
            Print("b2 defer {N}")
        Sleep(0.1)
        Print("b2 end {N}")
    Sleep(0.5)
    Print("G end {N}")
    X
Main()<suspends>:void =
    defer:
        Print("Main defer")
    Print("{G(7, "int")}")
    Print(G("s", "string"))
    Print("main end")
