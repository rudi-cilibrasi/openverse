# followup-coerce2 (#724): Does UEFN 43.12 refuse a field's function value
# of type type{_(:int)<computes>:int} passed to the generic Apply of
# method-arg-generic? OpenVerse's rule: refused, 3502.
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:int)<computes>:int} as a value of type
# type{_(:int)<transacts>:int}
holder := class:
    F:type{_(:int)<computes>:int}
Inc(X:int)<computes>:int = X + 1
Apply(F(:t)<transacts>:u, X:t where t:type, u:type):u = F(X)

Main():void =
    H := holder{F := Inc}
    Print("OVPROBE value {Apply(H.F, 1)}")
