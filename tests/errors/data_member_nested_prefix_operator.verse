# expect: 8:10: the value of the constant Neg calls prefix'-', which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a prefix operator the program overloads. Refused
# already.
vec := class<computes>:
    A:int = 0
prefix'-'(V:vec)<computes>:vec = vec{A := -V.A}
Neg:vec = -vec{A := 1}
Main():void = Print("{Neg.A}")
