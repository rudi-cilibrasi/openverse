# Edge of the 3552 rule (#724): a generic function constructs c(t) (with var
# Data:t) in its body, its type mentions no c. OpenVerse admits it and
# prints
#   result 1
# If Epic refuses it, the rule is not only about a function's type.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) admits it (compiled only).
c(t:type) := class:
    var Data:t

F(X:t where t:type)<transacts>:int =
    Obj := c(t){Data := X}
    1

Main():void =
    Print("OVPROBE result {F(7)}")
