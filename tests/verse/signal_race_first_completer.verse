# Two arms end inside the third arm's Signals, the second arm first: it
# wins, and the race's value is its own, not that of the arm that ended
# after it (the Book's ch. 14, "the first completer wins")
Main()<suspends>:void =
    A := event(int){}
    B := event(int){}
    Park := event(int){}
    V := race:
        block:
            A.Await()
            Print("one ends")
            1
        block:
            B.Await()
            Print("two ends")
            2
        block:
            B.Signal(0)
            A.Signal(0)
            Print("three waits")
            Park.Await()
            3
    Print("race {V}")
