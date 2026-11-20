# Several arguments passed to a function whose one parameter is an array:
# packed into the array.
# Tests LANGUAGE.md, Functions: "several arguments make a single array
# parameter (Sum(1, 2, 3))". Epic's compiler may refuse the packing.
# OpenVerse prints (Lean and C agree):
#   6 9 0
Total(Xs:[]int):int =
    var S:int = 0
    for (X : Xs):
        set S += X
    S

Main():void =
    Print("OVPROBE {Total(1, 2, 3)} {Total(array{4, 5})} {Total(array{})}")
