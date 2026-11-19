# A race arm cancelled (it loses) whose code spawned a task:
# is the spawned task its child, stopped before the arm's own defers as a
# child branch is (branch-cancel-order, UEFN 43.12), or does it go on?
# OpenVerse (#724) gives a spawn no parent, as the Book's Verse VM tests do
# (Tests/Bugs/BPVMOnly/AsyncContextCancellation.versetest): it goes on.
# OpenVerse prints:
#   winner done | arm cleanup | after race | spawned done | spawned cleanup | after wait
# If a spawned task were a child of the task whose code spawned it:
#   winner done | spawned cleanup | arm cleanup | after race | after wait
Spawned()<suspends>:void =
    defer:
        Print("OVPROBE spawned cleanup")
    Sleep(0.3)
    Print("OVPROBE spawned done")

Loser()<suspends>:void =
    defer:
        Print("OVPROBE arm cleanup")
    spawn{Spawned()}
    Sleep(10.0)

Main()<suspends>:void =
    race:
        Loser()
        block:
            Sleep(0.1)
            Print("OVPROBE winner done")
    Print("OVPROBE after race")
    Sleep(0.5)
    Print("OVPROBE after wait")
