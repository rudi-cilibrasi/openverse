# Control of join-named-default-param: a parameter of a function type with a
# named parameter, F1(F(?A:int):int), given F9 directly, no join. Not a Book
# case (the Book's JoinTest module defines these functions). OpenVerse
# prints
#   value 11
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints value 11, as OpenVerse
# does.
F1(F(?A:int):int):int = F(?A := 1)
F9(?A:int = 9, ?B:int = 10):int = A + B

Main():void =
    Print("OVPROBE value {F1(F9)}")
