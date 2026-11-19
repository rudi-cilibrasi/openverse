# expect: 9:27: the default of field 'Vals' of thing calls Two, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a field's default whose `for` calls a function with
# several values. Admitted before this follow-up, as such a call leaves no
# call (`Choice.inlineCalls` puts the function's code in its place);
# `$fxOf`, which stands for it, is noted now.
Two(N:int)<computes>:int = N | N + 1
thing := class<computes>:
    Vals:[]int = for (X := Two(3)) { X }
Main():void = Print("{thing{}.Vals.Length}")
