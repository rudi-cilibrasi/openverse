# expect: 4:18: ToChar can fail: call it with X.ToChar[]
# N.ToChar[] fails outside 0 to 255, so it is called with brackets.
Main():void =
    C := 65.ToChar()
