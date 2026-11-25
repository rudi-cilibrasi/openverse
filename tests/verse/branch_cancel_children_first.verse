# A cancelled task stops its children before any of its defers runs, newest
# first, each the same way (#724): the arms of the sync, race or rush it
# waits in (its newest), last started first, then its branches and the rush
# arms that went on. Measured on UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086, "Use Verse VM" on), the follow-up
# probes (tests/conformance/versevm/followup-conc/) printed what 1 to 7, 9
# and 10 print here: branch-cancel-order (1), cancel-grandchild-order (2),
# cancel-two-children-order (3), cancel-spawned-not-child (4: a spawned
# task is nobody's child), cancel-sync-arm-child (5),
# cancel-branch-before-sync-arms (6: the arms before the branch),
# cancel-rush-child (7), end-grandchild-order (9) and end-two-children-order
# (10: a task that ends runs its defers first, then stops its children).
# Epic refuses T.Cancel() in user code (8, cancel-task-child, 3593). A third
# round printed 11 to 13 too: a race's arms as a sync's
# (cancel-branch-before-race-arms), a branch started in an arm as that arm's
# child (cancel-branch-in-and-before-sync-arm), the arms one call deeper
# (cancel-branch-before-nested-sync).
Wait()<suspends>:void = Sleep(10.0)
Child(Tag:string)<suspends>:void =
    branch:
        defer:
            Print("{Tag} cleanup")
        Wait()
Nest(Tag:string)<suspends>:void =
    branch:
        defer:
            Print("{Tag} child cleanup")
        Child("{Tag} grandchild")
        Wait()
Spawned()<suspends>:void =
    defer:
        Print("4: spawned cleanup")
    Sleep(0.3)
    Print("4: spawned done")
# (the race arms that lose)
One()<suspends>:void =
    defer:
        Print("1: arm cleanup")
    Child("1: branch")
    Wait()
Two()<suspends>:void =
    defer:
        Print("2: arm cleanup")
    Nest("2:")
    Wait()
Three()<suspends>:void =
    defer:
        Print("3: arm cleanup")
    Child("3: first")
    Child("3: second")
    Wait()
Four()<suspends>:void =
    defer:
        Print("4: arm cleanup")
    spawn{Spawned()}
    Wait()
Five()<suspends>:void =
    defer:
        Print("5: loser cleanup")
    sync:
        block:
            defer:
                Print("5: sync arm cleanup")
            Child("5: branch")
            Wait()
        Wait()
Six()<suspends>:void =
    defer:
        Print("6: loser cleanup")
    Child("6: branch")
    sync:
        block:
            defer:
                Print("6: arm one cleanup")
            Wait()
        block:
            defer:
                Print("6: arm two cleanup")
            Wait()
Seven()<suspends>:void =
    defer:
        Print("7: loser cleanup")
    rush:
        Sleep(0.05)
        block:
            defer:
                Print("7: slow arm cleanup")
            Wait()
    Print("7: rush done")
    Wait()
Eleven()<suspends>:void =
    defer:
        Print("11: loser cleanup")
    Child("11: branch")
    race:
        block:
            defer:
                Print("11: arm one cleanup")
            Wait()
        block:
            defer:
                Print("11: arm two cleanup")
            Wait()
Twelve()<suspends>:void =
    defer:
        Print("12: loser cleanup")
    Child("12: task branch")
    sync:
        block:
            defer:
                Print("12: arm one cleanup")
            Child("12: arm branch")
            Wait()
        block:
            defer:
                Print("12: arm two cleanup")
            Wait()
Inner()<suspends>:void =
    defer:
        Print("13: inner cleanup")
    sync:
        block:
            defer:
                Print("13: arm one cleanup")
            Wait()
        block:
            defer:
                Print("13: arm two cleanup")
            Wait()
Thirteen()<suspends>:void =
    defer:
        Print("13: loser cleanup")
    Child("13: branch")
    Inner()
Lose(Tag:string, F:type{_()<suspends>:void})<suspends>:void =
    race:
        F()
        block:
            Sleep(0.1)
            Print("{Tag} winner done")
    Print("{Tag} after race")
Runner()<suspends>:void =
    defer:
        Print("8: runner cleanup")
    Child("8: branch")
    Wait()
Ending(Tag:string, Grand:logic)<suspends>:void =
    defer:
        Print("{Tag} runner cleanup")
    if (Grand?) then Nest(Tag) else:
        Child("{Tag} first")
        Child("{Tag} second")
    Sleep(0.1)
    Print("{Tag} runner ending")
Main()<suspends>:void =
    Lose("1:", One)
    Lose("2:", Two)
    Lose("3:", Three)
    Lose("4:", Four)
    Sleep(0.5)
    Lose("5:", Five)
    Lose("6:", Six)
    Lose("7:", Seven)
    T := spawn{Runner()}
    Sleep(0.1)
    T.Cancel()
    Print("8: cancelled")
    spawn{Ending("9:", true)}
    Sleep(0.3)
    spawn{Ending("10:", false)}
    Sleep(0.3)
    Lose("11:", Eleven)
    Lose("12:", Twelve)
    Lose("13:", Thirteen)
    Print("end")
