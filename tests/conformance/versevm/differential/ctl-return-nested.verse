# return from inside nested if, for and loop bodies, and code after it not
# run.
# Tests LANGUAGE.md, Control: "return (in a function's body ...)"; a return
# leaves every block around it.
# OpenVerse prints (Lean and C agree):
#   2 -1 | liftoff unlucky
FirstNegative(A:[]int):int =
    for (I -> X : A):
        if (X < 0):
            return I
    -1

Countdown(N:int):string =
    var K:int = N
    loop:
        if (K = 0):
            return "liftoff"
        if (K = 13):
            return "unlucky"
        set K -= 1

Main():void =
    Print("OVPROBE {FirstNegative(array{3, 0, -2, -5})} {FirstNegative(array{1})}")
    Print("OVPROBE {Countdown(3)} {Countdown(20)}")
