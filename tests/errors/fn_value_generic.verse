# expect: 'Id' is generic: a generic function is a value only where a closed function type it fits is expected
# (with no type expected, or a type over type parameters, it has no instance)
Id(X:t where t:type):t = X
Map(Xs:[]t, F:type{_(:t):u} where t:type, u:type):[]u = for (X : Xs) { F(X) }
Main():void =
    Ys := Map(array{1, 2}, Id)
    Print("{Ys.Length}")
