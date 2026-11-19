# expect: 5:23: the value of the constant Vals calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through an array's element. Refused already.
Next(X:int)<computes>:int = X + 1
Vals:[]int = array{Next(1)}
Main():void = Print("{Vals.Length}")
