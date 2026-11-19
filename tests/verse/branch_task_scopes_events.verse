# A branch woken by a Signal from a rush or sync arm of the same task, and
# the task's children when it ends (#724): the Book's Verse VM cases of
# Tests/Bugs/BPVMOnly/NestedUpdateStateCorruption.versetest, each a spawned
# task. Their lines are the Verse VM's of the Book (its tick separators
# left out): in the first and the fourth, the rush's arm that goes on (X)
# is the child of a task that ends before it would print (the spawned task,
# the sync's first arm), so it never prints.
Wait(N:int)<suspends>:void =
    for (I := 1..N):
        Sleep(0.01)

MinimalRush()<suspends>:void =
    Event := event(){}
    Print("1: A")
    branch:
        Event.Await()
        Print("1: W")
    rush:
        block:
            Print("1: B")
            Wait(1)
            Print("1: C")
            Event.Signal()
            Print("1: E")
        block:
            defer { Print("1: arm two stopped") }
            Print("1: D")
            Wait(2)
            Print("1: X")
    Print("1: F")
    Wait(1)
    Print("1: G")

MinimalSync()<suspends>:void =
    Event := event(){}
    Print("2: A")
    branch:
        Event.Await()
        Print("2: W")
    sync:
        block:
            Print("2: B")
            Wait(1)
            Print("2: C")
            Event.Signal()
            Print("2: E")
        block:
            Print("2: D")
            Wait(2)
            Print("2: F")
    Print("2: Z")

MultipleArms()<suspends>:void =
    Event := event(){}
    Print("3: A")
    branch:
        Event.Await()
        Print("3: W")
    sync:
        block:
            Print("3: 1")
            Wait(1)
            Print("3: S")
            Event.Signal()
            Print("3: E")
        block:
            Print("3: 2")
            Wait(2)
            Print("3: F")
        block:
            Print("3: 3")
            Wait(3)
            Print("3: G")
    Print("3: Z")

NestedConcurrency()<suspends>:void =
    Event := event(){}
    Print("4: A")
    branch:
        Event.Await()
        Print("4: W")
    sync:
        block:
            rush:
                block:
                    Print("4: R1")
                    Wait(1)
                    Print("4: S")
                    Event.Signal()
                    Print("4: E")
                block:
                    defer { Print("4: R2 stopped") }
                    Print("4: R2")
                    Wait(2)
                    Print("4: X")
            Print("4: F")
        block:
            Print("4: D")
            Wait(3)
            Print("4: G")
    Print("4: Z")

SignalFromDefer()<suspends>:void =
    Event := event(){}
    Print("5: A")
    branch:
        Event.Await()
        Print("5: W")
    sync:
        block:
            defer:
                Print("5: d")
                Event.Signal()
            Print("5: B")
            Wait(1)
            Print("5: C")
        block:
            Print("5: D")
            Wait(2)
            Print("5: F")
    Print("5: Z")
    Wait(1)
    Print("5: G")

Main()<suspends>:void =
    spawn{MinimalRush()}
    Wait(6)
    spawn{MinimalSync()}
    Wait(6)
    spawn{MultipleArms()}
    Wait(6)
    spawn{NestedConcurrency()}
    Wait(6)
    spawn{SignalFromDefer()}
    Wait(6)
    Print("done")
