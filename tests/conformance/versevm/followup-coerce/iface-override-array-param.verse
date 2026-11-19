# followup-coerce (#724): Does UEFN 43.12 admit an override, in a class of
# a(int), of a parametric interface's method whose parameter is []t (the
# type parameter inside an array, not a function type)? OpenVerse admits it.
# OpenVerse (Lean and C agreeing) prints length 2
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
a(t:type) := interface:
    F(X:[]t)<transacts>:int

b := class(a(int)):
    F<override>(X:[]int)<transacts>:int = X.Length

Main():void =
    Obj:b = b{}
    Print("OVPROBE length {Obj.F(array{1, 2})}")
