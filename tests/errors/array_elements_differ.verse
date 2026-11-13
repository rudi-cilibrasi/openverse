# expect: 7:32: no ToString for comparable (Verse defines it for int, float, char, char32 and string)
# (an array of unrelated comparable types is a []comparable, "their common
# supertype", Book of Verse ch. 1: nothing but = can be done with its
# elements)
Main():void =
    A := array{1, "s"}
    if (E := A[0]) then Print("{E}")
