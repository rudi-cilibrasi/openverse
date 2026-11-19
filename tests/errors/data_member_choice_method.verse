# expect: 10:29: the value of the constant Vals calls point.Near, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a method with several values. Admitted before this
# follow-up, as such a call leaves no call (`Choice.inlineCalls` puts the
# function's code in its place); `$fxOf`, which stands for it, is noted now.
point := class<computes>:
    X:int = 0
    Near()<computes>:int = X | X + 1
Origin:point = point{}
Vals:[]int = for (X := Origin.Near()) { X }
Main():void = Print("{Vals.Length}")
