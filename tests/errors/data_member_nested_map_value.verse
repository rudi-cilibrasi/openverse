# expect: 5:30: the value of the constant Table calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a map's value. Refused already.
Next(X:int)<computes>:int = X + 1
Table:[int]int = map{1 => Next(1)}
Main():void = Print("{Table.Length}")
