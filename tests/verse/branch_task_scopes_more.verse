# The shapes of the follow-up probes for Epic's Verse VM
# (tests/conformance/versevm/followup-conc/branch-*.verse,
# rush-loser-outlives-return.verse), 1 to 7 as Epic printed them (UEFN 43.12): a
# branch and a rush's arm that goes on are children of the task whose code
# started them, stopped when that task ends; a task that ends runs its own
# defers first, then stops its children, newest first; a cancelled task
# stops them first (6); a spawned task's children are stopped before its
# result is published to its awaiters.

# a branch started in a helper of a spawned task: the spawned task's child
SpawnHelper()<suspends>:void =
    branch:
        defer:
            Print("1: branch cleanup")
        loop:
            Sleep(0.1)
            Print("1: branch tick")
    Print("1: helper returning")
SpawnRunner()<suspends>:void =
    SpawnHelper()
    Print("1: runner after helper")
    Sleep(0.15)
    Print("1: runner ending")

# a branch in a sync's first arm: stopped when that arm ends
SyncArm()<suspends>:void =
    sync:
        block:
            branch:
                defer:
                    Print("2: branch cleanup")
                loop:
                    Sleep(0.1)
                    Print("2: branch tick")
            Sleep(0.05)
            Print("2: arm one done")
        block:
            Sleep(0.2)
            Print("2: arm two done")
    Print("2: after sync")

# a branch in a race's winning arm: stopped when that arm ends
RaceWinner()<suspends>:void =
    race:
        block:
            branch:
                defer:
                    Print("3: winner branch cleanup")
                loop:
                    Sleep(0.1)
                    Print("3: winner branch tick")
            Sleep(0.05)
            Print("3: winner done")
        block:
            defer:
                Print("3: loser cleanup")
            Sleep(1.0)
    Print("3: after race")

# a branch in a branch: the outer branch's child
Nested()<suspends>:void =
    branch:
        defer:
            Print("4: outer cleanup")
        branch:
            defer:
                Print("4: inner cleanup")
            loop:
                Sleep(0.1)
                Print("4: inner tick")
        Sleep(0.05)
        Print("4: outer done")
    Print("4: function returned")

# a rush's arm that goes on outlives the function that ran the rush
RushThenReturn()<suspends>:void =
    rush:
        block:
            Sleep(0.05)
            Print("5: fast arm")
        block:
            defer:
                Print("5: slow cleanup")
            Sleep(0.2)
            Print("5: slow arm done")
    Print("5: function returning")

# a race arm cancelled: its child's defer, then its own
CancelHelper()<suspends>:void =
    branch:
        defer:
            Print("6: branch cleanup")
        Sleep(10.0)
Loser()<suspends>:void =
    defer:
        Print("6: arm cleanup")
    CancelHelper()
    Sleep(10.0)

# a spawned task's children stopped before its awaiter resumes
AwaitHelper()<suspends>:void =
    branch:
        defer:
            Print("7: branch cleanup")
        Sleep(10.0)
Awaited()<suspends>:int =
    AwaitHelper()
    Sleep(0.1)
    Print("7: runner ending")
    5

Main()<suspends>:void =
    spawn{SpawnRunner()}
    Sleep(0.5)
    Print("1: main after wait")
    SyncArm()
    Sleep(0.3)
    Print("2: after wait")
    RaceWinner()
    Sleep(0.3)
    Print("3: after wait")
    Nested()
    Sleep(0.4)
    Print("4: after wait")
    RushThenReturn()
    Print("5: returned")
    Sleep(0.4)
    Print("5: after wait")
    race:
        Loser()
        block:
            Sleep(0.1)
            Print("6: winner done")
    Print("6: after race")
    T := spawn{Awaited()}
    V := T.Await()
    Print("7: awaited {V}")
    # (a branch at Main's top level: stopped when Main ends)
    branch:
        defer:
            Print("8: branch cleanup")
        loop:
            Sleep(0.5)
            Print("8: branch tick")
    Print("8: main returning")
