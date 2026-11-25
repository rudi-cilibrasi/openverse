# expect: 7:26: the value of the constant Vals calls Two, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through an overloaded function with several values in a
# `for`'s generator. Refused already.
Two(N:int)<computes>:int = N * 2
Two(S:string)<computes>:int = S.Length | 100
Vals:[]int = for (X := Two("abc")) { X }
Main():void = Print("{Vals.Length}")
