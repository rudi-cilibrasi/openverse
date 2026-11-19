# followup-coerce (#724): Does UEFN 43.12 admit interface-fn-param-generic's
# override in a class of a(any) (its message shows the declaration's t as
# any)? OpenVerse's rule: an instance any needs no wrapper, admitted.
# OpenVerse (Lean and C agreeing) prints called
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19):
# admitted it
TheG(X:any):void = {}
a(t:type) := interface:
    F(G(:t):void)<transacts>:void

b := class(a(any)):
    F<override>(G(:any):void)<transacts>:void = {}

Main():void =
    Obj:b = b{}
    Obj.F(TheG)
    Print("OVPROBE called")
