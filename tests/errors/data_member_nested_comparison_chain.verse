# expect: 5:23: the value of the constant Pick calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a comparison chain. Refused already.
Next(X:int)<computes>:int = X + 1
Pick:int = if (0 < Next(1) < 5) then 1 else 0
Main():void = Print("{Pick}")
