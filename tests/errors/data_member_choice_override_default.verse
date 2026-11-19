# expect: 11:37: the default of field 'Vals' of derived calls Two, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a field default a subclass overrides. Admitted before
# this follow-up, as such a call leaves no call (`Choice.inlineCalls` puts
# the function's code in its place); `$fxOf`, which stands for it, is noted
# now.
Two(N:int)<computes>:int = N | N + 1
base := class<computes>:
    Vals:[]int = array{}
derived := class<computes>(base):
    Vals<override>:[]int = for (X := Two(1)) { X }
Main():void = Print("{derived{}.Vals.Length}")
