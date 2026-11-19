# Edge of the 3552 rule (#724): a struct s(t) whose field holds c(t), with
# c's var Data:t; F(X:t where t:type):s(t). Epic refuses it through a
# class's field (followup-book3/parametric-var-where-nested). OpenVerse
# follows classes' fields only and admits it:
#   data 2
# If Epic refuses it (3552), a struct's fields count too.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3552 (L12) "An implicit type parameter
# (`t`) used in the type of mutable data (`<project>/c.Data`) may not be
# used in the ". OpenVerse refuses it now.
c(t:type) := class:
    var Data:t

s(t:type) := struct:
    Inner:c(t)

F(X:t where t:type)<transacts>:s(t) = s(t){Inner := c(t){Data := X}}

Main():void =
    Obj := F(1)
    set Obj.Inner.Data = 2
    Print("OVPROBE data {Obj.Inner.Data}")
