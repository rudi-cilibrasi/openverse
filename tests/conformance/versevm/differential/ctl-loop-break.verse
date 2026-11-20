# loop and break: a counted loop, nested loops where break leaves only the
# inner one, and a for inside a loop.
# Tests LANGUAGE.md, Control: "loop/break"; Equality and the empty value: "A
# nested loop's break leaves that nested loop".
# OpenVerse prints (Lean and C agree):
#   4 3 6 12
Main():void =
    var I:int = 0
    loop:
        set I += 1
        if (I >= 4):
            break
    var Pairs:int = 0
    var Outer:int = 0
    loop:
        set Outer += 1
        var J:int = 0
        loop:
            set J += 1
            set Pairs += 1
            if (J = Outer):
                break
        if (Outer = 3):
            break
    var Sum:int = 0
    loop:
        for (K := 1..3):
            set Sum += K
        if (Sum > 10):
            break
    Print("OVPROBE {I} {Outer} {Pairs} {Sum}")
