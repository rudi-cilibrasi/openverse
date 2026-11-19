# 3582 follow-up (#724), compile only: a module constant defined by an `if`
# whose condition (a failure context) calls a <computes> function: whether
# the rule reaches a call there. OpenVerse refuses it: "the value of the
# constant Pick calls Next, which might not complete" (3582). If Epic
# admits it, the run prints "pick 1".
Next(X:int)<computes>:int = X + 1

Pick:int = if (Next(1) > 1) then 1 else 2

Main():void =
    Print("OVPROBE pick {Pick}")
