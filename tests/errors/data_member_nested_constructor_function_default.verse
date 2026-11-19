# expect: 10:23: the default of field 'T' of holder calls MakeThing, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a field's default that calls a constructor function.
# Refused already.
thing := class<computes>:
    Size:int = 0
MakeThing<constructor>(N:int)<computes> := thing:
    Size := N
holder := class<computes>:
    T:thing = MakeThing(1)
Main():void = Print("{holder{}.T.Size}")
