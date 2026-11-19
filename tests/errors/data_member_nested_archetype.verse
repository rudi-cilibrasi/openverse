# expect: 7:30: the value of the constant Origin calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through an archetype's field value. Refused already.
Next(X:int)<computes>:int = X + 1
point := class<computes>:
    X:int = 0
Origin:point = point{X := Next(1)}
Main():void = Print("{Origin.X}")
