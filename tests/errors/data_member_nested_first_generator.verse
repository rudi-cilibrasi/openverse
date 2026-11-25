# expect: 5:32: the value of the constant Pick calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through `first(…){…}` with a generator. Refused already.
Next(X:int)<computes>:int = X + 1
Pick:int = first(X := 1..3, Next(X) > 2){X} or 0
Main():void = Print("{Pick}")
