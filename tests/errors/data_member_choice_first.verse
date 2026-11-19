# expect: 8:22: the value of the constant Pick calls Two, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through `first{…}` with a call of a function with several
# values. Admitted before this follow-up, as such a call leaves no call
# (`Choice.inlineCalls` puts the function's code in its place); `$fxOf`,
# which stands for it, is noted now.
Two(N:int)<computes>:int = N | N + 1
Pick:int = first{X := Two(3); X} or 0
Main():void = Print("{Pick}")
