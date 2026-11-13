# expect: a named parameter inside a tuple parameter (?Z) is not supported yet
# Book of Verse ch. 6's named elements in a tuple parameter: see docs/research/tuple-parameters.md
SumValues(A:int, (X:int, (Y:int, ?Z:int = 0))):int = A + X + Y + Z
Main():void =
    Print("{SumValues(1, (2, (3, ?Z := 4)))}")
