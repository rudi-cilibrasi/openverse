# expect: 5:27: the value of the constant Vals calls Items, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a `for`'s source. Refused already.
Items()<computes>:[]int = array{1, 2}
Vals:[]int = for (X : Items()) { X }
Main():void = Print("{Vals.Length}")
