# expect: b.F overrides a.F, whose type has a's type parameter t inside a function type
# (#724) an override, in a class of a(int), of a parametric interface's
# method whose result is (t->void) (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502,
# "type{_()<transacts>:int->void} as … type{_()<transacts>:any->void}":
# followup-coerce/iface-override-fn-result).
TakeInt(X:int):void = {}
a(t:type) := interface:
    F()<transacts>:(t->void)
b := class(a(int)):
    F<override>()<transacts>:(int->void) = TakeInt
Main():void =
    G := b{}.F()
    G(5)
