# Book: Tests/ParametricFunctions.versetest:431 (untagged): a parametric
# class with a var field of its parameter, constructed in a generic
# function, F(X:t where t:type):c(t) = c(t){Data := X}. The Book refuses it
# on both VMs, 3552 (not supported). OpenVerse admits it and prints
#   data 2
# If UEFN 43.12 refuses it, OpenVerse admits what Epic does not support yet.
# Control: parametric-var-where-construct-control (c(int), no generic
# function).
c(t:type) := class:
    var Data:t

F(X:t where t:type)<transacts>:c(t) = c(t){Data := X}

Main():void =
    Obj := F(1)
    set Obj.Data = 2
    Print("OVPROBE data {Obj.Data}")
