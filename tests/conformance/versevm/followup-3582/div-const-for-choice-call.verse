# 3582 follow-up (#724), compile only: a module constant defined by a `for`
# whose generator calls a <computes> function with several values (a choice
# in its body). OpenVerse compiles such a call by putting the function's
# body in place of the call, and admitted it before this follow-up; it now
# refuses it: "the value of the constant Vals calls Two, which might not
# complete" (3582). If Epic admits it, the run prints "count 2".
Two(N:int)<computes>:int = N | N + 1

Vals:[]int = for (X := Two(3)):
    X

Main():void =
    Print("OVPROBE count {Vals.Length}")
