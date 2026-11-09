# expect: 4:22: Digit has several values, so it cannot be used as a function value
Digit():int = 0 | 1
Main():void =
    F:type{_():int} = Digit
    Print("x")
