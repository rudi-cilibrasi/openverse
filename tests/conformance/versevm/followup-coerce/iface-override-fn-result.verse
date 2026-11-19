# followup-coerce (#724): Does UEFN 43.12 refuse an override, in a class of
# a(int), of a parametric interface's method whose result is (t->void)
# (interface-fn-param-generic has it in a parameter)? OpenVerse's rule:
# refused, 3502.
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_()<transacts>:type{_(:int):void}} as a value of type
# type{_()<transacts>:type{_(:any):void}}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L13 "Using a value of type type{_()<transacts>:int->void}
# as a value of type type{_()<transacts>:any->void} is not yet implemented."
TakeInt(X:int):void = Print("OVPROBE took {X}")
a(t:type) := interface:
    F()<transacts>:(t->void)

b := class(a(int)):
    F<override>()<transacts>:(int->void) = TakeInt

Main():void =
    Obj:b = b{}
    G := Obj.F()
    G(5)
