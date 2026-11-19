# expect: 5:18: the value of the constant Four calls Inc, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through an extension method. Refused already.
(X:int).Inc()<computes>:int = X + 1
Four:int = (3).Inc()
Main():void = Print("{Four}")
