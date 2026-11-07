# expect: 4:4: this expression can fail
# X / Y fails when Y = 0 (#116): it needs a failure context
Main():void =
    X := 7 / 2
