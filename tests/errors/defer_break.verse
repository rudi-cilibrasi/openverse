# expect: break is only allowed inside loop (not for), and cannot leave a defer: block
Main():void =
    loop:
        defer:
            break
        Print("x")
