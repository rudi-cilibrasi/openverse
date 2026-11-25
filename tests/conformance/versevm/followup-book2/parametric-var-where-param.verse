# Book: Tests/ParametricFunctions.versetest:438 (untagged): a generic
# function whose parameter is the parametric class with a var field,
# F(X:c(t) where t:type). The Book refuses it on both VMs, 3552. OpenVerse
# admits it and prints
#   called
# Control: parametric-var-where-construct-control.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3552 (L9) "An implicit type parameter
# (`t`) used in the type of mutable data (`<project>/c.Data`) may not be
# used in the type of a function.".
c(t:type) := class:
    var Data:t

F(X:c(t) where t:type)<transacts>:void = {}

Main():void =
    F(c(int){Data := 1})
    Print("OVPROBE called")
