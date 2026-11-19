# followup-coerce (#724): Does UEFN 43.12 admit an override of
# interface-fn-param-generic's F in a parametric class that passes its own
# type parameter on (c(t) := class(a(t))), used at c(int)? OpenVerse's rule:
# the declaration and the override then have the same type parameter, no
# wrapper, admitted.
# OpenVerse (Lean and C agreeing) prints called
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
TheG(X:int):void = {}
a(t:type) := interface:
    F(G(:t):void)<transacts>:void

c(t:type) := class(a(t)):
    F<override>(G(:t):void)<transacts>:void = {}

Main():void =
    Obj:c(int) = c(int){}
    Obj.F(TheG)
    Print("OVPROBE called")
