# expect: expected type{_(:t):t}, found type{_(:t, ?Y:t):t}
# A generic function's required named parameter keeps it from a type without it (#503)
PickY(X:t, ?Y:t where t:type):t = Y
UseD(V:t where t:type):t =
    F:type{_(:t):t} = PickY
    F(V)
Main():void =
    Print("{UseD(1)}")
