# expect: 7:32: no ToString for any (Verse defines it for int, float, char, char32 and string)
# (an array of unrelated types, one not comparable, is an []any, #138:
# nothing can be done with its elements)
c := class{}
Main():void =
    A := array{1, c{}}
    if (E := A[0]) then Print("{E}")
