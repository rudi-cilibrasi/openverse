# expect: 5:19: the value of the constant Pick calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through an `if` condition. Refused already.
Next(X:int)<computes>:int = X + 1
Pick:int = if (Next(1) > 0) then 1 else 2
Main():void = Print("{Pick}")
