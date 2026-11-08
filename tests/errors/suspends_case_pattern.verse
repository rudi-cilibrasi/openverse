# expect: a case pattern cannot suspend
Get(N:int)<suspends>:int =
    Sleep(0.0)
    N
Main()<suspends>:void =
    X:int = 2
    case (X):
        Get(1) => Print("one")
        Get(2) => Print("two")
        _ => Print("other")
