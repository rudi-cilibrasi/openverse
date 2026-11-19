# expect: 6:27: the value of the constant Pick calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through the right of `or`. Refused already.
Next(X:int)<computes>:int = X + 1
Items:[]int = array{1}
Pick:int = Items[5] or Next(1)
Main():void = Print("{Pick}")
