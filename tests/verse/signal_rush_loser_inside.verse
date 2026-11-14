# A rush's loser goes on as a task of its own; a later Signal resumes it
# inside the Signal (the Book's ch. 14, the rush example: the loser adds 100
# before the signaller's next line)
counter := class:
    var N:int = 0
Run(T:counter, Gate:event(int))<suspends>:int =
    W := rush:
        block:
            Gate.Await()
            set T.N += 100
            1
        block:
            Sleep(0.0)
            2
    Gate.Signal(0)
    Print("counter after signal {T.N}")
    W
Main()<suspends>:void =
    T := counter{}
    G := event(int){}
    W := Run(T, G)
    Print("winner {W}, counter {T.N}")
