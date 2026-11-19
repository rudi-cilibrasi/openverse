# branches in a generic function (at two types) that await a cancelled task
# in their first runs: each waits until its task ends, which stops it (#724:
# no longer the function's exit).
# (Each function's branches now go on after it returns, until Main ends.)
# (#724: a branch and a rush's arm that goes on are children of the task whose
# code started them, stopped when that task ends, after its own defers: Epic's
# Verse VM, UEFN 43.12; no longer when the function that started them exits.)
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
