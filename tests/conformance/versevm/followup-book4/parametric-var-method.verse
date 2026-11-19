# Edge of the 3552 rule (#724): a method of another class with an implicit
# type parameter of its own, Use(X:c(u) where u:type). OpenVerse refuses it
# as it does a function. If Epic admits it, it prints
#   result 1
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3552 (L8) "An implicit type parameter
# (`u`) used in the type of mutable data (`<project>/c.Data`) may not be
# used in the ".
c(t:type) := class:
    var Data:t

user := class:
    Use(X:c(u) where u:type):int = 1

Main():void =
    Print("OVPROBE result {user{}.Use(c(int){Data := 1})}")
