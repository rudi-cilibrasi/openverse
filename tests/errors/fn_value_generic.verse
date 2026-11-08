# expect: 'Id' is generic: a generic function cannot be used as a value yet (#210)
Id(X:t where t:type):t = X
Main():void =
    F:int->int = Id
    Print("{F(1)}")
