# expect: 4:23: ToCodeUnit cannot fail: call it with X.ToCodeUnit()
# A char's code unit always exists.
Main():void =
    N := 'a'.ToCodeUnit[]
