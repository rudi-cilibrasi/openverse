# expect: 8:19: the value of the constant Some calls Two, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through `option{…}` of a call of a function with several
# values. Admitted before this follow-up, as such a call leaves no call
# (`Choice.inlineCalls` puts the function's code in its place); `$fxOf`,
# which stands for it, is noted now.
Two(N:int)<computes>:int = N | N + 1
Some:?int = option{Two(1)}
Main():void = Print("{Some? or 0}")
