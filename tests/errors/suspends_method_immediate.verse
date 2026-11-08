# expect: a.Run suspends: it can only be called in a <suspends> function
a := class:
    Run()<suspends>:void = Sleep(1.0)
Main():void =
    A := a{}
    A.Run()
