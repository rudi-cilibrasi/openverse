# expect: 4:21: expected 'do', found 'X'
# After braced definitions, let's body follows `do`.
Main():void =
    N := let{X := 3} X + 1
