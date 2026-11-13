# expect: 'A' is already defined; Verse does not allow shadowing
# A destructured name is bound for the whole body
F((A:int, B:int)):int =
    A := 3
    A + B
Main():void =
    Print("{F((1, 2))}")
