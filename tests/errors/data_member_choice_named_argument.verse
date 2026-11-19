# expect: 8:23: the value of the constant Vals calls Named, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a function with several values given a named argument.
# Admitted before this follow-up, as such a call leaves no call
# (`Choice.inlineCalls` puts the function's code in its place); `$fxOf`,
# which stands for it, is noted now.
Named(?A:int = 1)<computes>:int = A | A + 1
Vals:[]int = for (V := Named(?A := 5)) { V }
Main():void = Print("{Vals.Length}")
