# Control of join-named-default-param: a parameter of a function type with a
# named parameter, F1(F(?A:int):int), given F9 directly, no join. Not a Book
# case (the Book's JoinTest module defines these functions). OpenVerse
# prints
#   value 11
F1(F(?A:int):int):int = F(?A := 1)
F9(?A:int = 9, ?B:int = 10):int = A + B

Main():void =
    Print("OVPROBE value {F1(F9)}")
