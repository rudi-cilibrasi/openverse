# expect: 5:31: the value of the constant Pick calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through an `if` branch. Refused already.
Next(X:int)<computes>:int = X + 1
Pick:int = if (1 > 0) then Next(1) else 2
Main():void = Print("{Pick}")
