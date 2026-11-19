# expect: 5:39: the value of the constant Vals calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a `for`'s filter. Refused already.
Next(X:int)<computes>:int = X + 1
Vals:[]int = for (X : array{1, 2}, Next(X) > 2) { X }
Main():void = Print("{Vals.Length}")
