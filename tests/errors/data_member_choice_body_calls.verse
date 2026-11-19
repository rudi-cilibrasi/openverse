# expect: 9:23: the value of the constant Vals calls Two, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a function with several values whose body calls
# another. Refused before this follow-up for the call in Two's body; now for
# the call of Two, the data member's own (the calls in the code put in its
# place are Two's, `Ctx.inlineScopes`).
Next(X:int)<computes>:int = X + 1
Two(N:int)<computes>:int = Next(N) | N
Vals:[]int = for (X := Two(3)) { X }
Main():void = Print("{Vals.Length}")
