# expect: unknown type 't'
# The parameter's type must be known at the top level to check its default (#503)
Id(X:t, ?A:t = X where t:type):t = A
Use(V:t, F:type{_(:t, ?A:t = V):t} where t:type):t = F(V)
Main():void =
    Print("{Use(3, Id)}")
