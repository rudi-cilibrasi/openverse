# expect: 6:19: the value of the constant TwoSteps calls a value of type type{_(:int)<computes>:int}, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a call through a function value. Refused already.
Next(X:int)<computes>:int = X + 1
Step:type{_(:int)<computes>:int} = Next
TwoSteps:int = Step(1)
Main():void = Print("{TwoSteps}")
