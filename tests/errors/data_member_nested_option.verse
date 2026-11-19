# expect: 5:23: the value of the constant Some calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through `option{…}`. Refused already.
Next(X:int)<computes>:int = X + 1
Some:?int = option{Next(1)}
Main():void = Print("{Some? or 0}")
