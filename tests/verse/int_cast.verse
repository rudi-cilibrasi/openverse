# int[X] of an int: a cast to the type of every int, failable as a cast is,
# which no 64-bit int fails. UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086)
# admits it (tests/conformance/versevm/book/book-int-cast-int.verse; the
# Book of Verse's tests, WhereConstrainedInts.versetest:219-222)
age := type{_X:int where 0 <= _X, _X <= 120}
Main():void =
    X:int = 5
    if (Y := int[X]) then Print("int {Y}")
    if (A := age[30], B := int[A]) then Print("age {B}")
    if (int[9223372036854775807] = 9223372036854775807) then Print("largest")
    if (int[-9223372036854775808] < 0) then Print("smallest")
