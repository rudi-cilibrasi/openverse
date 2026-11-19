# expect: 9:23: the value of the constant Vals calls A, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a recursive function with several values at growing
# types, computed eagerly (`F$all`). Refused already.
A(X:t, N:int where t:type)<computes>:int =
    if (N > 0) then (N | B(array{X}, N - 1)) else 0
B(X:u, N:int where u:type)<computes>:int =
    if (N > 0) then (N | A(array{X}, N - 1)) else 0
Vals:[]int = for (V := A(7, 2)) { V }
Main():void = Print("{Vals.Length}")
