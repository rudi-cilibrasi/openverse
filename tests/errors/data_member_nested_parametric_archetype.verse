# expect: 7:41: the value of the constant Full calls Next, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a parametric class's archetype. Refused already.
Next(X:int)<computes>:int = X + 1
box(t:type) := class<computes>:
    V:?t = false
Full:box(int) = box(int){V := option{Next(1)}}
Main():void = Print("{Full.V? or 0}")
