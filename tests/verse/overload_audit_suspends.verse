# Only the selected overload determines whether a call suspends.
Get(X:int)<computes>:int = X + 1
Get(X:string)<suspends>:int =
    defer:
        Print("cleanup")
    Print("begin {X}")
    Sleep(0.1)
    Print("end {X}")
    X.Length
Main()<suspends>:void =
    Print("{Get(3)}")
    T := spawn{Get("word")}
    R := T.Await()
    Print("result {R}")
