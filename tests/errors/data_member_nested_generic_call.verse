# expect: 5:16: the value of the constant Three calls Same, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a generic function. Refused already.
Same(X:t where t:type)<computes>:t = X
Three:int = Same(3)
Main():void = Print("{Three}")
