# expect: a defer: block cannot be empty
Main():void =
    defer {}
    Print("x")
