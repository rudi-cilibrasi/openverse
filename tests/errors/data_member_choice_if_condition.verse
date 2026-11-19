# expect: 8:20: the value of the constant Pick calls Two, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through an `if` condition that calls a function with several
# values. Admitted before this follow-up, as such a call leaves no call
# (`Choice.inlineCalls` puts the function's code in its place); `$fxOf`,
# which stands for it, is noted now.
Two(N:int)<computes>:int = N | N + 1
Pick:int = if (X := Two(3), X > 3) then X else 0
Main():void = Print("{Pick}")
