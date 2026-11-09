# expect: 6:4: c.Vals has several values, so it cannot be used as a functio
c := class:
    Vals()<transacts>:int = 1 | 2
Main()<transacts>:void =
    O := c{}
    F := O.Vals
    Print("x")
