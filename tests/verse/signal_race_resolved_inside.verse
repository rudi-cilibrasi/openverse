# An arm resumed inside its sibling's Signal ends there and wins the race:
# the signalling arm goes on to its next wait and is then cancelled, and the
# arm after it never starts (the Book's ch. 14, "An arm that is already
# executing when the race resolves ... continues to its next suspension
# point and is then cancelled"; the Book's tests,
# FORT-1126351-RaceArmsDoNotStartAfterResolution)
Main()<suspends>:void =
    E := event(int){}
    Stop := event(int){}
    V := race:
        block:
            X := E.Await()
            Print("arm one got {X}")
            X
        block:
            defer:
                Print("arm two cancelled")
            Print("arm two signals")
            E.Signal(4)
            Print("arm two goes on")
            Stop.Await()
            Print("arm two never ends")
            2
        block:
            Print("arm three never starts")
            Stop.Await()
            3
    Print("race {V}")
