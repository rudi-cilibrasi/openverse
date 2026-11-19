# expect: 8:23: the value of the constant Vals calls Down, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a recursive function with several values, taken lazily
# (`$loop`). Admitted before this follow-up, as such a call leaves no call
# (`Choice.inlineCalls` puts the function's code in its place); `$fxOf`,
# which stands for it, is noted now.
Down(N:int)<computes>:int = if (N <= 0) then 0 else (N | Down(N - 1))
Vals:[]int = for (X := Down(3)) { X }
Main():void = Print("{Vals.Length}")
