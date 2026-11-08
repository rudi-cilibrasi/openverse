# expect: c implements M separately for ia and ib, so the value M would not say which
ia := interface:
    M():int
ib := interface:
    M():int
c := class(ia, ib):
    (ia:)M<override>():int = 1
    (ib:)M<override>():int = 2
Run(F:type{_():int}):int = F()
Main():void =
    X := c{}
    Print("{Run(X.M)}")
