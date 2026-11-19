# expect: 5:31: the value of the constant Pick calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a `case`'s arm. Refused already.
Next(X:int)<computes>:int = X + 1
Pick:int = case (1) { 1 => Next(1), _ => 0 }
Main():void = Print("{Pick}")
