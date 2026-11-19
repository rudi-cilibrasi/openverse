# (#724) what UEFN 43.12 (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086) admits of followup-coerce's
# generic and override probes: a generic function with a function parameter
# called (generic-result-plain), a generic result of a function type at
# comparable (generic-result-fn-comparable), overrides of a parametric
# interface's method with []t (iface-override-array-param), in a class that
# passes its type parameter on (iface-own-param-fn) and at any
# (iface-fn-param-any); and functions and methods named as arguments of a
# generic call at its parameter's type (ParametricFunctions.versetest:189,
# Apply(Incr, 1), valid on both VMs).
TakeInt(X:int):void = Print("took {X}")
TakeComparable(X:comparable):void = Print("took a comparable")
TheG(X:int):void = {}
TheAny(X:any):void = {}
Keep(X:t, F(:t):void where t:type):t =
    F(X)
    X
Wrap(X:t, F(:t):void where t:type):(t->void) = F
a(t:type) := interface:
    F(X:[]t)<transacts>:int
b := class(a(int)):
    F<override>(X:[]int)<transacts>:int = X.Length
e(t:type) := interface:
    G(H(:t):void)<transacts>:void
c(t:type) := class(e(t)):
    G<override>(H(:t):void)<transacts>:void = {}
d := class(e(any)):
    G<override>(H(:any):void)<transacts>:void = {}
counter := class:
    Inc(X:int)<computes>:int = X + 1
Incr(X:int)<computes>:int = X + 1
Apply(F(:t)<transacts>:u, X:t where t:type, u:type):u = F(X)
Main():void =
    Print("kept {Keep(5, TakeInt)}")
    C:comparable = 1
    W := Wrap(C, TakeComparable)
    W(C)
    Obj:b = b{}
    Print("length {Obj.F(array{1, 2})}")
    c(int){}.G(TheG)
    d{}.G(TheAny)
    Print("{Apply(Incr, 1)} {Apply(counter{}.Inc, 2)}")
