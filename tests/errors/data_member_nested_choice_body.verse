# expect: 6:36: the value of the constant Vals calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a `for` over a choice of literals, whose body calls.
# Refused already.
Next(X:int)<computes>:int = X + 1
Vals:[]int = for (X := 1 | 2) { Next(X) }
Main():void = Print("{Vals.Length}")
