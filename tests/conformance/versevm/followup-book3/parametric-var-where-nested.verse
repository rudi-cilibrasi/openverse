# Edge of the 3552 rule (#724): holder(t) has an immutable field of c(t),
# whose var Data:t is mutable data; F(X:t where t:type):holder(t). OpenVerse
# measures a class's own var fields only, and prints
#   data 2
# If Epic refuses it (3552), the rule reaches mutable data through other
# types' fields.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3552 (L12) "An implicit type parameter
# (`t`) used in the type of mutable data (`<project>/c.Data`) may not be
# used in the type of a ".
c(t:type) := class:
    var Data:t

holder(t:type) := class:
    Inner:c(t)

F(X:t where t:type)<transacts>:holder(t) = holder(t){Inner := c(t){Data := X}}

Main():void =
    Obj := F(1)
    set Obj.Inner.Data = 2
    Print("OVPROBE data {Obj.Inner.Data}")
