# followup-coerce (#724): Does UEFN 43.12 refuse One passed to a function
# that is not generic, whose parameter A is of One's instance at int?
# OpenVerse's rule: refused, 3502. Control: generic-higher-order-control in
# followup-book2 (One called).
# OpenVerse refuses it: 3502 rule: using a value of type
# type{_(:type{_(:t)<transacts>:t}, :t)<transacts>:t} where t as a value of
# type type{_(:type{_(:int)<transacts>:int}, :int)<transacts>:int}
One(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(X)
Succ(X:int)<transacts>:int = X + 1
RunOne(A(F(:int)<transacts>:int, X:int)<transacts>:int)<transacts>:int = A(Succ, 0)

Main():void =
    Print("OVPROBE value {RunOne(One)}")
