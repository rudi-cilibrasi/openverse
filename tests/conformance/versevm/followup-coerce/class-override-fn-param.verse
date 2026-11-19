# followup-coerce (#724): Does UEFN 43.12 refuse an override, in a class of
# base(int), of a parametric class's method whose parameter is a function of
# t (a class, not an interface, as interface-fn-param-generic)? OpenVerse's
# rule: refused, 3502.
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:type{_(:int):void}):void} as a value of type
# type{_(:type{_(:any):void}):void}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3502 L13 "Using a value of type (int->void)->void as a value
# of type (any->void)->void is not yet implemented."
TheG(X:int):void = Print("OVPROBE called {X}")
base(t:type) := class:
    F(G(:t):void):void = {}

derived := class(base(int)):
    F<override>(G(:int):void):void = G(1)

Main():void =
    Obj:derived = derived{}
    Obj.F(TheG)
