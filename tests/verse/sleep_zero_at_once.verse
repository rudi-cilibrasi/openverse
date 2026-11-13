# Sleep(0.0) completes at once, without suspending (the Book's tested
# examples in ch. 14, 03 to 11): each task below ends within its spawn, so
# Main sees what it did right after the spawn returns. A race arm that
# sleeps zero wins in the race's first pass, and the arms after it never
# start; a sync's arms that sleep zero end as they start; a return after a
# zero sleep in an arm leaves the function before the other arms start.
cell := class:
    var Ids:tuple(int, int, int) = (0, 0, 0)
    var Winner:int = 0
    var ArmThreeRan:logic = false
    var Result:int = 0
    var ArmTwoRan:logic = false
    var PastSync:logic = false

Fetch(N:int)<suspends>:int =
    Sleep(0.0)
    N

LoadAll(C:cell)<suspends>:void =
    set C.Ids = sync:
        Fetch(1)
        Fetch(2)
        Fetch(3)

RaceThree(C:cell)<suspends>:void =
    set C.Winner = race:
        block:
            Sleep(0.01)
            1
        block:
            Sleep(0.0)
            2
        block:
            set C.ArmThreeRan = true
            Sleep(0.0)
            3

Abandon(C:cell)<suspends>:int =
    sync:
        block:
            Sleep(0.0)
            return 5
        block:
            Sleep(0.0)
            set C.ArmTwoRan = true
    set C.PastSync = true   # (never reached: the first arm returns, a warning)
    0

RunAbandon(C:cell)<suspends>:void =
    set C.Result = Abandon(C)

Main()<suspends>:void =
    C := cell{}
    spawn{LoadAll(C)}
    spawn{RaceThree(C)}
    spawn{RunAbandon(C)}
    Print("ids {C.Ids(0)} {C.Ids(1)} {C.Ids(2)}")
    Print("race won by {C.Winner}")
    if (C.ArmThreeRan?) then Print("arm three ran") else Print("arm three never started")
    Print("abandon gave {C.Result}")
    if (C.ArmTwoRan?) then Print("arm two ran") else Print("arm two never started")
    if (C.PastSync?) then Print("past the sync") else Print("the sync was left")
    Sleep(0.0)
    Print("Main's zero sleep did not wait")
