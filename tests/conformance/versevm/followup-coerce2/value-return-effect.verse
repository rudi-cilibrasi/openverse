# followup-coerce2 (#724): Does UEFN 43.12 refuse a function that returns
# its parameter, of type type{_(:int)<computes>:int}, at the result type
# type{_(:int)<transacts>:int} (a value returned, not a name)? OpenVerse's
# rule: refused, 3502. Control: value-return-same.
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:int)<computes>:int} as a value of type
# type{_(:int)<transacts>:int}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L9 "Using a value of type type{_(:int)<computes>:int} as
# a value of type type{_(:int)<transacts>:int} is not yet implemented."
Inc(X:int)<computes>:int = X + 1
Widen(G(:int)<computes>:int):type{_(:int)<transacts>:int} = G

Main():void =
    F := Widen(Inc)
    Print("OVPROBE value {F(1)}")
