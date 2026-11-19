# expect: One is generic, its type parameter t inside a function type of its own
# (#724) One, generic with its type parameter inside a function type of its
# own, bound to a local of its instance's type, no generic call around it
# (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502: followup-coerce/generic-higher-order-bound).
One(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(X)
Succ(X:int)<transacts>:int = X + 1
Main():void =
    G:type{_(:type{_(:int)<transacts>:int}, :int)<transacts>:int} = One
    Print("{G(Succ, 0)}")
