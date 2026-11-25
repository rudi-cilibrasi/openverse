# expect: 6:19: the value of the constant None calls Nothing, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a call that gives a type as an argument. Refused
# already.
Nothing(t:type)<computes>:?t = false
None:?int = Nothing(int)
Main():void = Print("{None? or 0}")
