# Book: Tests/Bugs/SOL-4199-BreakFromIf.versetest:39 (1 case): break inside a
# for's body inside a loop, which leaves the loop. The Book's tests expect it
# valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "break is only allowed inside
# loop (not for)"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   count 1
# OpenVerse now prints it too (#724, Lean and C): a break in a for's body
# leaves the loop around the for (tests/verse/for_break_loop).
Main():void =
    var Count:int = 0
    loop:
        for (I := 1..2):
            set Count += I
            break
        break
    Print("OVPROBE count {Count}")
