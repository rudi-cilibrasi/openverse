# expect: 14:17: using a value of type type{_(:type{_(:t)<transacts>:t}, :t)<transacts>:t} where t as a value of type type{_(:type{_(:int)<transacts>:int}, :int)<transacts>:int} is not yet implemented
# One, generic with its type parameter inside a function type of its own
# (F(:t)<transacts>:t), passed as a value to Plus: its instance at int needs
# a wrapper that converts a function value, which Epic's Verse compiler makes
# for no generic function (UEFN 43.12, error 3502 at each of the eight
# arguments: followup-book2/generic-higher-order; ParametricFunctions.versetest:276,
# bp_vm_only). One called with Succ is admitted
# (fn_coerce_generic_higher_order_control).
One(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(X)
Two(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(F(X))
Plus(A(F(:t)<transacts>:t, X:t)<transacts>:t, B(F(:t)<transacts>:t, X:t)<transacts>:t, F(:t)<transacts>:t, X:t where t:type)<transacts>:t = A(F, B(F, X))
Succ(X:int)<transacts>:int = X + 1
Main():void =
    Print("{Plus(One, Two, Succ, 0)}")
