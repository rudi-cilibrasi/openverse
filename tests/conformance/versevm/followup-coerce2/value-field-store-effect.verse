# followup-coerce2 (#724): Does UEFN 43.12 refuse a parameter of type
# type{_(:int)<computes>:int} stored into a field of type
# type{_(:int)<transacts>:int} at a construction? OpenVerse's rule: refused,
# 3502.
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:int)<computes>:int} as a value of type
# type{_(:int)<transacts>:int}
Inc(X:int)<computes>:int = X + 1
holder := class:
    F:type{_(:int)<transacts>:int}
Make(G(:int)<computes>:int):holder = holder{F := G}

Main():void =
    H := Make(Inc)
    Print("OVPROBE value {H.F(1)}")
