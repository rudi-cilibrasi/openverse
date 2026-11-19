# expect: 8:27: the default of field 'Vals' of sized calls Two, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through an interface's field default. Admitted before this
# follow-up, as such a call leaves no call (`Choice.inlineCalls` puts the
# function's code in its place); `$fxOf`, which stands for it, is noted now.
Two(N:int)<computes>:int = N | N + 1
sized := interface<computes>:
    Vals:[]int = for (X := Two(1)) { X }
thing := class<computes>(sized):
    W:int = 0
Main():void = Print("{thing{}.Vals.Length}")
