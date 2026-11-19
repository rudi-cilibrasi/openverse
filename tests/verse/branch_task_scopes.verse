# A branch, and a rush's arms that go on, are children of the task whose
# code starts them, and are cancelled when that task ends (#724): the rule
# of Epic's Verse VM, whose probes vm-branch-outlives-return and
# vm-branch-await-after-return print "returned" before the branch's last
# line and its cleanup (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086),
# and of the Book's Verse VM tests, Tests/Bugs/BPVMOnly/
# AsyncContextCancellation.versetest ("Tasks are cancelled when their
# PARENT TASK ends (completes or cancels). Parent/child relationships are
# determined by concurrency forms, NOT by function/loop/block boundaries").
# Tasks: a spawn (no parent), each arm of a sync, race and rush, a branch.
# Below, the Book's seven cases, each a spawned task as there; Wait(N)
# sleeps N ticks. The lines each prints are the Verse VM's of the Book
# (its tick separators left out); a cancelled task's defer shows when it
# is cancelled.
Wait(N:int)<suspends>:void =
    for (I := 1..N):
        Sleep(0.01)

# 1. A branch in a sync arm is cancelled when that arm completes.
BranchInSync()<suspends>:void =
    Print("1: A")
    sync:
        block:
            branch:
                defer { Print("1: B cancelled") }
                Wait(5)
                Print("1: B")
            Wait(1)
            Print("1: 1")
        block:
            Wait(2)
            Print("1: 2")
    Print("1: F")
    Wait(4)
    Print("1: G")

# 2. A branch in a rush arm is cancelled when that arm completes; the
# rush's other arm, a child of the spawned task, goes on.
BranchInRush()<suspends>:void =
    Print("2: A")
    rush:
        block:
            branch:
                defer { Print("2: B cancelled") }
                Wait(5)
                Print("2: B")
            Wait(1)
            Print("2: 1")
        block:
            Wait(3)
            Print("2: 2")
    Print("2: F")
    Wait(4)
    Print("2: G")

# 3. A rush in a sync arm: its arm that goes on is that sync arm's child,
# cancelled when the sync arm completes.
RushInSync()<suspends>:void =
    Print("3: A")
    sync:
        block:
            rush:
                block:
                    Wait(1)
                    Print("3: R1")
                block:
                    defer { Print("3: R2 cancelled") }
                    Wait(3)
                    Print("3: R2")
            Print("3: F")
        block:
            Wait(2)
            Print("3: S2")
    Print("3: Z")
    Wait(2)
    Print("3: G")

# 4. A rush in a rush arm: the inner arm that goes on is the outer arm's
# child, cancelled when the outer arm completes; the outer rush's other arm
# goes on.
NestedRush()<suspends>:void =
    Print("4: A")
    rush:
        block:
            Print("4: O1")
            rush:
                block:
                    Wait(1)
                    Print("4: I1")
                block:
                    defer { Print("4: I2 cancelled") }
                    Wait(4)
                    Print("4: I2")
            Print("4: X")
            Wait(1)
        block:
            Print("4: O2")
            Wait(3)
            Print("4: O2done")
    Print("4: F")
    Wait(3)
    Print("4: G")

# 5. A rush in a race arm that loses: the race's losing arm is cancelled,
# and the rush's arms with it.
RushInRaceArm()<suspends>:void =
    Print("5: A")
    race:
        block:
            Wait(1)
            Print("5: 1")
        block:
            rush:
                block:
                    defer { Print("5: R1 cancelled") }
                    Print("5: R1")
                    Wait(2)
                    Print("5: R1done")
                block:
                    defer { Print("5: R2 cancelled") }
                    Print("5: R2")
                    Wait(3)
                    Print("5: R2done")
            Print("5: X")
    Print("5: F")
    Wait(3)
    Print("5: G")

# 6. A rush in a function called from a loop: its arms that go on are the
# spawned task's children, and go on after the function returns, until the
# task ends.
FastThenSlow(X:int)<suspends>:void =
    rush:
        block:
            Print("6: F{X}")
            Wait(1)
        block:
            Wait(3)
            Print("6: S{X}")

LoopWithRush()<suspends>:void =
    Print("6: A")
    for (X := 1..3):
        FastThenSlow(X)
        Print("6: B")
    Print("6: C")
    Wait(4)
    Print("6: G")

# 7. sync > rush > branch: the branch is the rush arm's child, cancelled
# when it completes; the rush's other arm is the sync arm's child,
# cancelled when the sync arm completes.
DeepNesting()<suspends>:void =
    Print("7: A")
    sync:
        block:
            rush:
                block:
                    branch:
                        defer { Print("7: B cancelled") }
                        Wait(5)
                        Print("7: B")
                    Wait(1)
                    Print("7: R1")
                block:
                    defer { Print("7: R2 cancelled") }
                    Wait(3)
                    Print("7: R2")
            Print("7: X")
            Wait(1)
        block:
            Wait(4)
            Print("7: S2")
    Print("7: Z")
    Wait(1)
    Print("7: G")

Main()<suspends>:void =
    spawn{BranchInSync()}
    Wait(9)
    spawn{BranchInRush()}
    Wait(9)
    spawn{RushInSync()}
    Wait(9)
    spawn{NestedRush()}
    Wait(9)
    spawn{RushInRaceArm()}
    Wait(9)
    spawn{LoopWithRush()}
    Wait(12)
    spawn{DeepNesting()}
    Wait(9)
    Print("done")
