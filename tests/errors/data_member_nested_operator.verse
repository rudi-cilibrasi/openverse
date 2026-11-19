# expect: 7:22: the value of the constant Sum calls operator'+', which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through an operator the program overloads. Refused already.
vec := class<computes>:
    A:int = 0
operator'+'(L:vec, R:vec)<computes>:vec = vec{A := L.A + R.A}
Sum:vec = vec{A := 1} + vec{A := 2}
Main():void = Print("{Sum.A}")
