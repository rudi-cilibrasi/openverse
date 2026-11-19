# followup-coerce (#724): Does UEFN 43.12 admit a <computes> function named
# where a type{_(:int)<transacts>:int} is expected, no join and no <decides>
# (the controls of followup-book2 add <decides>)? OpenVerse's rule: a
# function named where a function type is expected gets the wrapper.
# OpenVerse (Lean and C agreeing) prints value 2
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
Inc(X:int)<computes>:int = X + 1

Main():void =
    F:type{_(:int)<transacts>:int} = Inc
    Print("OVPROBE value {F(1)}")
