# expect: 6:20: the value of the constant Years calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a refinement type's cast. Refused already.
Next(X:int)<computes>:int = X + 1
age := type{_X:int where 0 <= _X, _X <= 120}
Years:int = age[Next(1)] or 0
Main():void = Print("{Years}")
