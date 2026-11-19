# Control of parametric-var-where-construct and parametric-var-where-param:
# the parametric class with a var field of its parameter, constructed at int
# and set. Not a Book case (the Book's valid uses,
# Tests/ParametricFunctions.versetest:454 on, pass the type as an argument).
# OpenVerse prints
#   data 2
# A refusal here means such a class is refused whatever uses it.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints data 2, as OpenVerse does.
c(t:type) := class:
    var Data:t

Main():void =
    Obj := c(int){Data := 1}
    set Obj.Data = 2
    Print("OVPROBE data {Obj.Data}")
