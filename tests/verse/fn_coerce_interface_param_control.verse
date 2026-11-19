# (#724) b, a class of a(int), overrides a's F(X:t): no function type has t,
# so no wrapper converts a function value; UEFN 43.12 admits it
# (followup-book2/interface-fn-param-generic-control). A class that passes its
# own type parameter on, c(t) := class(a(t)), has the declaration's type.
TheG(X:int)<transacts>:void = Print("G {X}")
a(t:type) := interface:
    F(X:t)<transacts>:void
b := class(a(int)):
    F<override>(X:int)<transacts>:void = Print("F {X}")
e(t:type) := interface:
    H(G(:t)<transacts>:void, X:t)<transacts>:void
c(t:type) := class(e(t)):
    H<override>(G(:t)<transacts>:void, X:t)<transacts>:void = G(X)
Main():void =
    Obj:b = b{}
    Obj.F(1)
    C:c(int) = c(int){}
    C.H(TheG, 2)
