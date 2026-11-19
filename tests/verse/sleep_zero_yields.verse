# Sleep(0.0) yields: it suspends and resumes on the next tick, as Epic's
# Verse VM and Blueprint VM both do (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, probe vm-sleep-zero-yields: "worker
# before sleep", "main after spawn", "worker after sleep"), and as the Book's
# API reference says ("0.0 resumes on the next update and, crucially, does
# yield"). The Book's tested examples of ch. 14 (03 to 11), which had it
# complete at once, are not followed. So a task spawned below has not ended
# when its spawn returns; a race arm that sleeps zero does not win before the
# arms after it start; a sync's arms that sleep zero all start first; a
# return after a zero sleep in an arm comes after the other arms started.
# Sleep(0.0) and Sleep(0.01) both wait one tick, so the race's first arm,
# first in source order at that tick, wins.
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

Worker()<suspends>:void =
    Print("worker before sleep")
    Sleep(0.0)
    Print("worker after sleep")

Report(C:cell):void =
    Print("ids {C.Ids(0)} {C.Ids(1)} {C.Ids(2)}")
    Print("race won by {C.Winner}")
    if (C.ArmThreeRan?) then Print("arm three ran") else Print("arm three never started")
    Print("abandon gave {C.Result}")
    if (C.ArmTwoRan?) then Print("arm two went past its sleep") else Print("arm two did not go past its sleep")
    if (C.PastSync?) then Print("past the sync") else Print("the sync was left")

Main()<suspends>:void =
    spawn{Worker()}
    Print("main after spawn")
    C := cell{}
    spawn{LoadAll(C)}
    spawn{RaceThree(C)}
    spawn{RunAbandon(C)}
    Report(C)
    Sleep(0.0)
    Print("Main's zero sleep waited a tick")
    Report(C)
    Sleep(0.1)
    Report(C)
