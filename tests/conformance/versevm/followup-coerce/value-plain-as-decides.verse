# followup-coerce (#724): Does UEFN 43.12 refuse a function value that is no
# function's name (a parameter of type type{_(:int)<computes>:int}) passed
# where a type{_(:int)<computes><decides>:int} is expected? (A name gets the
# wrapper: join-generic-effects-decides-control.) OpenVerse's rule left it
# admitted until Epic answered.
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:int)<computes>:int} as a value of type
# type{_(:int)<decides><computes>:int}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L9 "Using a value of type type{_(:int)<computes>:int} as
# a value of type type{_(:int)<computes><decides>:int} is not yet
# implemented."
Inc(X:int)<computes>:int = X + 1
Try(F(:int)<computes><decides>:int)<computes><decides>:int = F[1]
Forward(G(:int)<computes>:int)<computes><decides>:int = Try[G]

Main():void =
    if (V := Forward[Inc]):
        Print("OVPROBE value {V}")
