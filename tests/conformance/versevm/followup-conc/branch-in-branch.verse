# A branch started inside another branch's body: is its parent the outer
# branch (a branch is a task of its own), so that it is cancelled when the
# outer branch's body ends?
# OpenVerse (#724) prints (the outer body ends, its own defer runs, then its
# child is stopped):
#   function returned | outer done | outer cleanup | inner cleanup | after wait
# If the inner branch's parent were the task that started the outer branch
# (Main's):
#   function returned | outer done | outer cleanup | inner tick | inner tick |
#   inner tick | after wait (and inner cleanup when Main's task ends)
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19) printed
#   function returned | outer done | outer cleanup | inner cleanup | after wait
# as OpenVerse does.
Start()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE outer cleanup")
        branch:
            defer:
                Print("OVPROBE inner cleanup")
            loop:
                Sleep(0.1)
                Print("OVPROBE inner tick")
        Sleep(0.05)
        Print("OVPROBE outer done")
    Print("OVPROBE function returned")

Main()<suspends>:void =
    Start()
    Sleep(0.4)
    Print("OVPROBE after wait")
