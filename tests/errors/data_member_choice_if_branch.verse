# expect: 8:39: the value of the constant Vals calls Two, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through an `if` branch with several values as a `for`'s
# generator. Admitted before this follow-up, as such a call leaves no call
# (`Choice.inlineCalls` puts the function's code in its place); `$fxOf`,
# which stands for it, is noted now.
Two(N:int)<computes>:int = N | N + 1
Vals:[]int = for (Z := if (1 > 0) then Two(1) else 0) { Z }
Main():void = Print("{Vals.Length}")
