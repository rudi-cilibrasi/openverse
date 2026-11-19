# expect: 5:25: the value of the constant Table calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a map's key. Refused already.
Next(X:int)<computes>:int = X + 1
Table:[int]int = map{Next(1) => 1}
Main():void = Print("{Table.Length}")
