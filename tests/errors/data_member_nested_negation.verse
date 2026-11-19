# expect: 5:15: the value of the constant Low calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a negation. Refused already.
Next(X:int)<computes>:int = X + 1
Low:int = -Next(1)
Main():void = Print("{Low}")
