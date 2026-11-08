# expect: 3:9: first{…} with a choice can fail, but it is not in a failure context
Main():void =
    Z := first{X := 1 | 2; X}
    Print("{Z}")
