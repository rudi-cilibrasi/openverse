# Edge of the 3552 rule (#724): c(t) has a var field that does not mention t
# (var Count:int) and an immutable Data:t; F(X:t where t:type):c(t).
# OpenVerse admits it and prints
#   count 2
# If Epic refuses it, any var field of a parametric class counts.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) admits it (compiled only).
c(t:type) := class:
    var Count:int = 0
    Data:t

F(X:t where t:type)<transacts>:c(t) = c(t){Data := X}

Main():void =
    Obj := F(1)
    set Obj.Count = 2
    Print("OVPROBE count {Obj.Count}")
