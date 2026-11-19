# followup-coerce (#724): Does UEFN 43.12 refuse a call of a method of a
# parametric class whose result has the class's type parameter inside a
# function type, on box(int)? OpenVerse's rule covered generic functions
# only, admitting it, until Epic answered.
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:type{_(:t):void}):type{_(:t):void}} where t as a value of type
# type{_(:type{_(:int):void}):type{_(:int):void}}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L12 "Using a value of type (t->void)->(t->void) as a
# value of type (int->void)->(int->void) is not yet implemented."
TakeInt(X:int):void = Print("OVPROBE took {X}")
box(t:type) := class:
    Make(F(:t):void):(t->void) = F

Main():void =
    B := box(int){}
    G := B.Make(TakeInt)
    G(5)
