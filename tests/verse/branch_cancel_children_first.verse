# A cancelled task stops its children (its branches and the rush arms that
# went on), newest first, each the same way, before its own code unwinds
# (#724). Measured (1): on UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086,
# "Use Verse VM" on), the probe followup-conc/branch-cancel-order printed
# `winner done | branch cleanup | arm cleanup | after race | after wait`;
# a task that ends runs its defers first, then stops its children
# (branch-in-branch). The rest extends the rule, as the follow-up probes
# cancel-*.verse and end-*.verse ask Epic: a child is stopped as a
# cancelled task is, its own children first (2, 9), newest first (3, 10);
# a spawned task is nobody's child (4); a sync arm cancelled with its task
# stops its children first too (5); a cancelled task's children come before
# the arms it waits in, last started first, then its defers (6); a rush's
# arm that went on is a child (7); and T.Cancel() of a spawned task (8).
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
    Print("end")
