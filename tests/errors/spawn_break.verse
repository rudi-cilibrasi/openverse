# expect: a break inside spawn would leave it
G(X:void)<suspends>:void = {}
H()<suspends>:void =
    loop:
        spawn:
            G(break)
        break
Main():void = {}
