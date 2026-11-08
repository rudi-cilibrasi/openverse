# <suspends> function types (#210): values called in a loop, raced, in a
# spawned call; a function without <suspends> fits such a type
Wait(X:float)<suspends>:int =
    Sleep(X)
    1
Fast(X:float):int = 2
RunAll(Fs:[]type{_(:float)<suspends>:int})<suspends>:int =
    var Sum:int = 0
    for (F : Fs):
        set Sum += F(0.1)
    Sum
Race2(A:type{_(:float)<suspends>:int}, B:type{_(:float)<suspends>:int})<suspends>:int =
    race:
        A(0.5)
        B(0.2)
Main()<suspends>:void =
    Print("{RunAll(array{Wait, Fast})}")
    Print("{Race2(Wait, Wait)}")
    T := spawn{RunAll(array{Fast})}
    Print("{T.Await()}")
