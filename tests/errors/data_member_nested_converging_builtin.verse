# expect: 6:19: the value of the constant Size calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through the argument of a converging built-in (`Abs`). Refused
# already.
Next(X:int)<computes>:int = X + 1
Size:int = Abs(Next(1))
Main():void = Print("{Size}")
