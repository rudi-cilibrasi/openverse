# expect: 5:22: the value of the constant Has calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through `logic{…}`. Refused already.
Next(X:int)<computes>:int = X + 1
Has:logic = logic{Next(1) > 0}
Main():void = Print("{if (Has?) then 1 else 0}")
