# expect: 5:28: the value of the constant Pair calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a tuple's element. Refused already.
Next(X:int)<computes>:int = X + 1
Pair:tuple(int, int) = (Next(1), 2)
Main():void = Print("{Pair(1)}")
