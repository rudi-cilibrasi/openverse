# expect: 8:23: the value of the constant Vals calls Pick, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a generic function with several values. Admitted
# before this follow-up, as such a call leaves no call (`Choice.inlineCalls`
# puts the function's code in its place); `$fxOf`, which stands for it, is
# noted now.
Pick(X:t, Y:t where t:type)<computes>:t = X | Y
Vals:[]int = for (V := Pick(1, 2)) { V }
Main():void = Print("{Vals.Length}")
