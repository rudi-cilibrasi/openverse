# expect: 6:21: the value of the constant Pick calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through an index. Refused already.
Next(X:int)<computes>:int = X + 1
Items:[]int = array{1, 2}
Pick:int = Items[Next(0)] or 0
Main():void = Print("{Pick}")
