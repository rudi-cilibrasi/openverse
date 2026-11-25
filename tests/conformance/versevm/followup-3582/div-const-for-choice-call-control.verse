# 3582 follow-up (#724), control of div-const-for-choice-call: the same
# `for` over a call of a function with several values, in a local constant,
# which is no data member: whether Epic compiles a function with a choice
# in its body at all. OpenVerse admits it and prints "count 2".
Two(N:int)<computes>:int = N | N + 1

Main():void =
    Vals:[]int = for (X := Two(3)):
        X
    Print("OVPROBE count {Vals.Length}")
