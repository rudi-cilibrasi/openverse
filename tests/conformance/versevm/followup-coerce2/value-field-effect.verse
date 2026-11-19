# followup-coerce2 (#724): Does UEFN 43.12 refuse a field's function value,
# of type type{_(:int)<computes>:int}, read and passed where a
# type{_(:int)<transacts>:int} is expected? OpenVerse's rule: refused, 3502.
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:int)<computes>:int} as a value of type
# type{_(:int)<transacts>:int}
Inc(X:int)<computes>:int = X + 1
holder := class:
    F:type{_(:int)<computes>:int}
Run(F(:int)<transacts>:int)<transacts>:int = F(1)

Main():void =
    H := holder{F := Inc}
    Print("OVPROBE value {Run(H.F)}")
