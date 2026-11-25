# expect: 8:23: the value of the constant Vals calls Two, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a call in the argument of a function with several
# values. Refused before this follow-up, for Next; now for Two, which comes
# first.
Next(X:int)<computes>:int = X + 1
Two(N:int)<computes>:int = N | N + 1
Vals:[]int = for (X := Two(Next(1))) { X }
Main():void = Print("{Vals.Length}")
