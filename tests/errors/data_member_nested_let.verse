# expect: 5:24: the value of the constant Pick calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through `let(…){…}`. Refused already.
Next(X:int)<computes>:int = X + 1
Pick:int = let(Y := Next(1)){Y}
Main():void = Print("{Pick}")
