# Edge of the 3552 rule (#724): F(X:[]c(t) where t:type), the class inside
# an array type. OpenVerse finds the class anywhere in the type and refuses
# it. If Epic admits it, it prints
#   length 1
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3552 (L7) "An implicit type parameter
# (`t`) used in the type of mutable data (`<project>/c.Data`) may not be
# used in the ".
c(t:type) := class:
    var Data:t

F(X:[]c(t) where t:type):int = X.Length

Main():void =
    Print("OVPROBE length {F(array{c(int){Data := 1}})}")
