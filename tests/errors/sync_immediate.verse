# expect: sync suspends: it can only be used in a <suspends> function
Main():void =
    sync:
        Print("a")
        Print("b")
