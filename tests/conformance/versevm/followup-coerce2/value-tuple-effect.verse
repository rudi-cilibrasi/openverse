# followup-coerce2 (#724): Does UEFN 43.12 refuse a tuple literal whose
# element is a local of type type{_(:int)<computes>:int} where a
# tuple(type{_(:int)<transacts>:int}, int) is expected (tuple-of-fns-default
# names a function there, admitted)? OpenVerse's rule: refused, 3502.
# OpenVerse refuses it: 3502 rule: using a value of type
# tuple(type{_(:int)<computes>:int}, int) as a value of type
# tuple(type{_(:int)<transacts>:int}, int)
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L12 "Using a value of type
# tuple(type{_(:int)<computes>:int},type{1}) as a value of type
# tuple(type{_(:int)<transacts>:int},int) is not yet implemented."
Inc(X:int)<computes>:int = X + 1

Main():void =
    G:type{_(:int)<computes>:int} = Inc
    T:tuple(type{_(:int)<transacts>:int}, int) = (G, 1)
    Print("OVPROBE value {T(0)(T(1))}")
