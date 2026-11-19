# followup-coerce2 (#724): Does UEFN 43.12 refuse a call's result, of type
# type{_(:int)<computes>:int}, passed where a type{_(:int)<transacts>:int}
# is expected? OpenVerse's rule: refused, 3502.
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:int)<computes>:int} as a value of type
# type{_(:int)<transacts>:int}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L12 "Using a value of type type{_(:int)<computes>:int} as
# a value of type type{_(:int)<transacts>:int} is not yet implemented."
Inc(X:int)<computes>:int = X + 1
Make():type{_(:int)<computes>:int} = Inc
Run(F(:int)<transacts>:int)<transacts>:int = F(1)

Main():void =
    Print("OVPROBE value {Run(Make())}")
