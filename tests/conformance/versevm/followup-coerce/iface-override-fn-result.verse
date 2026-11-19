# followup-coerce (#724): Does UEFN 43.12 refuse an override, in a class of
# a(int), of a parametric interface's method whose result is (t->void)
# (interface-fn-param-generic has it in a parameter)? OpenVerse's rule:
# refused, 3502.
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_()<transacts>:type{_(:int):void}} as a value of type
# type{_()<transacts>:type{_(:any):void}}
TakeInt(X:int):void = Print("OVPROBE took {X}")
a(t:type) := interface:
    F()<transacts>:(t->void)

b := class(a(int)):
    F<override>()<transacts>:(int->void) = TakeInt

Main():void =
    Obj:b = b{}
    G := Obj.F()
    G(5)
