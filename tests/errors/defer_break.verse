# expect: break cannot leave a defer: block
Main():void =
    loop:
        defer:
            break
        Print("x")
