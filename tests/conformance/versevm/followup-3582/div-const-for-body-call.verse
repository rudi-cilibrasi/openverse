# 3582 follow-up (#724), compile only: a module constant defined by a `for`
# over an array literal whose body calls a <computes> function: whether
# the rule reaches a call nested in a `for`'s body. OpenVerse refuses it:
# "the value of the constant Vals calls Next, which might not complete"
# (3582). If Epic admits it, the run prints "count 2".
Next(X:int)<computes>:int = X + 1

Vals:[]int = for (X : array{1, 2}):
    Next(X)

Main():void =
    Print("OVPROBE count {Vals.Length}")
