# expect: 9:23: the value of the constant Vals calls Ping, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through functions with several values that call each other (a
# group's machine). Admitted before this follow-up, as such a call leaves no
# call (`Choice.inlineCalls` puts the function's code in its place);
# `$fxOf`, which stands for it, is noted now.
Ping(N:int)<computes>:int = if (N <= 0) then 0 else (N | Pong(N - 1))
Pong(N:int)<computes>:int = if (N <= 0) then 1 else (N | Ping(N - 1))
Vals:[]int = for (X := Ping(3)) { X }
Main():void = Print("{Vals.Length}")
