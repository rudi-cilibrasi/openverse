# expect: 8:35: the value of the constant Vals calls Two, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a `for`'s filter that calls a function with several
# values. Admitted before this follow-up, as such a call leaves no call
# (`Choice.inlineCalls` puts the function's code in its place); `$fxOf`,
# which stands for it, is noted now.
Two(N:int)<computes>:int = N | N + 1
Vals:[]int = for (X : array{1, 2}, Two(X) > 2) { X }
Main():void = Print("{Vals.Length}")
