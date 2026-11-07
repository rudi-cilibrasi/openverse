# expect: return is not allowed in a block: clause
a := class:
    N:int
    block:
        return
    block:
        Print("after")
Main():void =
    X := a{N := 1}
