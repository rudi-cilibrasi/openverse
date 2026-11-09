# expect: 5:4: c.Vals has several values, but an interface (i) has it
i := interface:
    Vals()<transacts>:int
c := class(i):
    Vals<override>()<transacts>:int = 1 | 2
Main()<transacts>:void =
    for (X := c{}.Vals()):
        Print("{X}")
