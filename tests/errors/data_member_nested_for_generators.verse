# expect: 5:58: the value of the constant Vals calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a `for` with two generators. Refused already.
Next(X:int)<computes>:int = X + 1
Vals:[]int = for (X : array{1, 2}, Y : array{3, 4}) { Next(X + Y) }
Main():void = Print("{Vals.Length}")
