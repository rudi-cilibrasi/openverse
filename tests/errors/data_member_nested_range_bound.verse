# expect: 5:30: the value of the constant Vals calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a range's bound. Refused already.
Next(X:int)<computes>:int = X + 1
Vals:[]int = for (X := 1..Next(2)) { X }
Main():void = Print("{Vals.Length}")
