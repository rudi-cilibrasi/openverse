# Book: Tests/ParametricFunctions.versetest:438 (untagged): a generic
# function whose parameter is the parametric class with a var field,
# F(X:c(t) where t:type). The Book refuses it on both VMs, 3552. OpenVerse
# admits it and prints
#   called
# Control: parametric-var-where-construct-control.
c(t:type) := class:
    var Data:t

F(X:c(t) where t:type)<transacts>:void = {}

Main():void =
    F(c(int){Data := 1})
    Print("OVPROBE called")
