# expect: i is an interface: it cannot be constructed
i := interface:
    M():int
Main():void =
    X := i{}
