# expect: return is not allowed in a defer: block
F():int =
    defer:
        return 1
    2
Main():void = Print("{F()}")
