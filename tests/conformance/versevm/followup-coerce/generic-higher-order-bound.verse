# followup-coerce (#724): Does UEFN 43.12 refuse One, generic with its type
# parameter inside a function type of its own (F(:t)<transacts>:t), bound to
# a local of the function type of its instance at int, no call of a generic
# function around it? It refuses One passed to Plus (generic-higher-order,
# where the parameter's type has Plus's type parameter). OpenVerse's rule:
# refused, 3502 (such a generic function is no value at an instance). If
# Epic admits it, the rule is about arguments whose type is still being
# inferred.
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:type{_(:t)<transacts>:t}, :t)<transacts>:t} where t as a value of
# type type{_(:type{_(:int)<transacts>:int}, :int)<transacts>:int}
One(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(X)
Succ(X:int)<transacts>:int = X + 1

Main():void =
    G:type{_(:type{_(:int)<transacts>:int}, :int)<transacts>:int} = One
    Print("OVPROBE value {G(Succ, 0)}")
