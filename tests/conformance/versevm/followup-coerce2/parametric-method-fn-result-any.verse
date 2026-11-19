# followup-coerce2 (#724): followup-coerce's parametric-method-fn-result on
# box(any): does UEFN 43.12 admit it (its messages show a type parameter as
# any)? OpenVerse admits it: an instance any needs no wrapper.
# OpenVerse (Lean and C agreeing) prints took
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19) admits
# it.
TakeAny(X:any):void = Print("OVPROBE took")
box(t:type) := class:
    Make(F(:t):void):(t->void) = F

Main():void =
    B := box(any){}
    G := B.Make(TakeAny)
    G(5)
