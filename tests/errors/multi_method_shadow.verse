# expect: 5:8: 'K' is already a field or method of c; Verse does not allow shadowing
c := class:
    K : int
    Vals()<transacts>:int =
        K := 5
        K | K + 1
Main()<transacts>:void =
    for (X := c{K := 1}.Vals()):
        Print("{X}")
