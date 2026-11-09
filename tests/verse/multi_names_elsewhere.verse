# a function with several values using a top-level name that another function's parameter also has, consumed elsewhere (#283)
Limit:int = 3
Small():int = 1 | Limit
Other(Limit:int):int = Limit * 2
Main():void =
    for (X := Small()) { Print("{X} {Other(X)}") }
