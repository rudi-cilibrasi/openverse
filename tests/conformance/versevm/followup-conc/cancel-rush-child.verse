# A race arm cancelled (it loses) that ran a rush whose slow arm goes on (a
# child of the race arm, as a branch it starts is, the Book's
# AsyncContextCancellation.versetest): is that rush arm stopped before the
# race arm's own defer, as a child branch is (branch-cancel-order, UEFN
# 43.12)?
# OpenVerse (#724) stops every child of a cancelled task first.
# OpenVerse prints:
#   rush done | winner done | slow arm cleanup | loser cleanup | after race | after wait
# If a rush arm that goes on were stopped after the defers of the task that
# ran the rush:
#   rush done | winner done | loser cleanup | slow arm cleanup | after race | after wait
Loser()<suspends>:void =
    defer:
        Print("OVPROBE loser cleanup")
    rush:
        block:
            Sleep(0.05)
        block:
            defer:
                Print("OVPROBE slow arm cleanup")
            Sleep(10.0)
    Print("OVPROBE rush done")
    Sleep(10.0)

Main()<suspends>:void =
    race:
        Loser()
        block:
            Sleep(0.2)
            Print("OVPROBE winner done")
    Print("OVPROBE after race")
    Sleep(0.1)
    Print("OVPROBE after wait")
