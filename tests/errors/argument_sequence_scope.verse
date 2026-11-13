# expect: 6:12: unknown identifier 'Y'
# A sequence in an argument is a block: its names stay inside it.
F(A:int):int = A
Main():void =
    R := F(Y := 1; Y + 1)
    Print("{Y}")
