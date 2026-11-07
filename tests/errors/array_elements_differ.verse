# expect: 5:32: no ToString for any (Verse defines it for int, float, char, char32 and string)
# (an array of unrelated types is an []any, #138: nothing can be done with its elements)
Main():void =
    A := array{1, "s"}
    if (E := A[0]) then Print("{E}")
