# A race arm cancelled (it loses) whose child branch, started in a helper
# that returned, has started a branch of its own: in which order do the
# grandchild's, the child's and the arm's own defers run?
# Epic (UEFN 43.12, branch-cancel-order) stops a cancelled task's child
# before the task's own defers run. OpenVerse (#724) does so at every
# depth: a child is cancelled the same way, its own children first.
# OpenVerse prints:
#   winner done | grandchild cleanup | child cleanup | arm cleanup | after race | after wait
# If a stopped child ran its own defers before stopping its children (as a
# task that ends does, branch-in-branch):
#   winner done | child cleanup | grandchild cleanup | arm cleanup | after race | after wait
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19) printed
#   winner done | grandchild cleanup | child cleanup | arm cleanup | after race | after wait
# as OpenVerse does.
Helper()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE child cleanup")
        branch:
            defer:
                Print("OVPROBE grandchild cleanup")
            Sleep(10.0)
        Sleep(10.0)

Loser()<suspends>:void =
    defer:
        Print("OVPROBE arm cleanup")
    Helper()
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
