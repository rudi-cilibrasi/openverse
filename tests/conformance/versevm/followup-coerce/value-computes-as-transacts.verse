# followup-coerce (#724): Does UEFN 43.12 refuse a function value that is no
# function's name (a parameter, of type type{_(:int)<computes>:int}) passed
# where a type{_(:int)<transacts>:int} is expected? Epic's 3502 so far is of
# branches of an if and of generic functions; this asks whether every value
# that is not a name needs the wrapper it does not make. OpenVerse's rule
# left it admitted until Epic answered. Control:
# value-computes-as-transacts-control (the parameter already <transacts>).
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:int)<computes>:int} as a value of type
# type{_(:int)<transacts>:int}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L11 "Using a value of type type{_(:int)<computes>:int} as
# a value of type type{_(:int)<transacts>:int} is not yet implemented."
Inc(X:int)<computes>:int = X + 1
Run(F(:int)<transacts>:int)<transacts>:int = F(1)
Forward(G(:int)<computes>:int)<transacts>:int = Run(G)

Main():void =
    Print("OVPROBE value {Forward(Inc)}")
