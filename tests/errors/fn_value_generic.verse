# expect: cannot infer type parameter u of Map from the arguments of this call
# The call cannot infer Map's result parameter from a polymorphic identifier.
Id(X:t where t:type):t = X
Map(Xs:[]t, F:type{_(:t):u} where t:type, u:type):[]u = for (X : Xs) { F(X) }
Main():void =
    Ys := Map(array{1, 2}, Id)
    Print("{Ys.Length}")
