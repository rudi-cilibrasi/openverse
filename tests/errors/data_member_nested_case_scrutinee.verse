# expect: 5:21: the value of the constant Pick calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a `case`'s scrutinee. Refused already.
Next(X:int)<computes>:int = X + 1
Pick:int = case (Next(1)) { 2 => 1, _ => 0 }
Main():void = Print("{Pick}")
