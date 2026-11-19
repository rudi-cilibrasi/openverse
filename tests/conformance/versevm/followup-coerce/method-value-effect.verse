# followup-coerce (#724): Does UEFN 43.12 admit a <computes> method of an
# object, as a value, where a type{_(:int)<transacts>:int} is expected (a
# method named, as a function named gets its wrapper)? OpenVerse admits it.
# OpenVerse (Lean and C agreeing) prints value 2
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
counter := class:
    Inc(X:int)<computes>:int = X + 1

Main():void =
    C := counter{}
    F:type{_(:int)<transacts>:int} = C.Inc
    Print("OVPROBE value {F(1)}")
