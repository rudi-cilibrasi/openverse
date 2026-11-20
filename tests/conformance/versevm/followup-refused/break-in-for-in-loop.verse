# Book: Tests/Bugs/SOL-4199-BreakFromIf.versetest:39 (1 case): break inside a
# for's body inside a loop, which leaves the loop. The Book's tests expect it
# valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "break is only allowed inside
# loop (not for)"
# If UEFN 43.12 admits it, it prints
#   count 1
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Main():void =
    var Count:int = 0
    loop:
        for (I := 1..2):
            set Count += I
            break
        break
    Print("OVPROBE count {Count}")
