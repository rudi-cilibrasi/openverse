# expect: 5:32: the value of the constant Vals calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through `for{…}`. Refused already.
Next(X:int)<computes>:int = X + 1
Vals:[]int = for{X := 1..3; Next(X)}
Main():void = Print("{Vals.Length}")
