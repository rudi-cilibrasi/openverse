# A defer inside a loop body runs at the end of each iteration, and on the
# break that ends the loop.
# Tests LANGUAGE.md, defer: "at the scope's end ... or on a return or break
# that leaves it".
# OpenVerse prints (Lean and C agree):
#   body 1 | defer 1 | body 2 | defer 2 | defer 3 | after 3
Main():void =
    var I:int = 0
    loop:
        set I += 1
        defer:
            Print("OVPROBE defer {I}")
        if (I = 3):
            break
        Print("OVPROBE body {I}")
    Print("OVPROBE after {I}")
