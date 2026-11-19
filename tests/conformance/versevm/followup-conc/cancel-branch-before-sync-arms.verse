# A race arm cancelled (it loses) that started a child branch (in a helper
# that returned) and then waits in a sync of two arms, each with a defer:
# is its branch stopped before the arms it waits in are cancelled, or after
# them (the arms, started later, as its newest children)? And which sync arm
# unwinds first?
# OpenVerse (#724) stopped a cancelled task's children (its branches, the
# rush arms that went on) first, then unwound its code from where it
# waits, the arms it waits in last started first, then its own defers, and
# printed, until Epic's result below:
#   winner done | branch cleanup | arm two cleanup | arm one cleanup | loser cleanup | after race | after wait
# If the arms it waits in were stopped first, as its newest children:
#   winner done | arm two cleanup | arm one cleanup | branch cleanup | loser cleanup | after race | after wait
# (arm one before arm two if a sync's arms unwind in the order they started)
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19) printed
#   winner done | arm two cleanup | arm one cleanup | branch cleanup | loser cleanup | after race | after wait
# the second reading: the arms the cancelled task waits in go first, last
# started first, as its newest children, then its branch. OpenVerse printed
# the first until then; it now prints Epic's (#724).
Helper()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        Sleep(10.0)

Loser()<suspends>:void =
    defer:
        Print("OVPROBE loser cleanup")
    Helper()
    sync:
        block:
            defer:
                Print("OVPROBE arm one cleanup")
            Sleep(10.0)
        block:
            defer:
                Print("OVPROBE arm two cleanup")
            Sleep(10.0)

Main()<suspends>:void =
    race:
        Loser()
        block:
            Sleep(0.1)
            Print("OVPROBE winner done")
    Print("OVPROBE after race")
    Sleep(0.1)
    Print("OVPROBE after wait")
