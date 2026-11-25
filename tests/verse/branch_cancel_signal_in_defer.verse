# A Signal made by a defer that runs while a task is cancelled wakes none of
# that task's waits (#724): its children are stopped before its defers run
# (Epic's Verse VM, UEFN 43.12, followup-conc/branch-cancel-order), and a
# child's defer may signal an event the task waits on; the task unwinds
# from where it waited.
# Also a sync's arm that waits on an event its sibling's defer signals, as
# the sibling is cancelled first, last started first (2), and a race arm
# that loses, waiting in a sync's arm on an event its child signals (4).
H(E:event(), Tag:string)<suspends>:void =
    branch:
        defer:
            Print("{Tag} branch cleanup")
            E.Signal()
        Sleep(10.0)
T1(E:event())<suspends>:void =
    defer:
        Print("1: task cleanup")
    H(E, "1:")
    E.Await()
    Print("1: task resumed (wrong)")
T2(E:event())<suspends>:void =
    defer:
        Print("2: task cleanup")
    sync:
        block:
            defer:
                Print("2: arm one cleanup")
            E.Await()
            Print("2: arm one resumed (wrong)")
        block:
            defer:
                Print("2: arm two cleanup")
                E.Signal()
            Sleep(10.0)
Arm(E:event())<suspends>:void =
    defer:
        Print("3: arm cleanup")
    H(E, "3:")
    E.Await()
    Print("3: arm resumed (wrong)")
M(E:event())<suspends>:void =
    defer:
        Print("4: arm cleanup")
    H(E, "4:")
    sync:
        block:
            defer:
                Print("4: sync arm cleanup")
            E.Await()
            Print("4: sync arm resumed (wrong)")
        Sleep(10.0)
Main()<suspends>:void =
    E1 := event(){}
    X := spawn{T1(E1)}
    Sleep(0.1)
    X.Cancel()
    Print("1: cancelled")
    E2 := event(){}
    Y := spawn{T2(E2)}
    Sleep(0.1)
    Y.Cancel()
    Print("2: cancelled")
    E3 := event(){}
    race:
        Arm(E3)
        block:
            Sleep(0.1)
            Print("3: winner done")
    Print("3: after race")
    E4 := event(){}
    race:
        M(E4)
        block:
            Sleep(0.1)
            Print("4: winner done")
    Print("4: after race")
    Sleep(0.1)
    Print("end")
