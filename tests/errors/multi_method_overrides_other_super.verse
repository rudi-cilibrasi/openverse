# expect: 7:4: big.Sizes uses (super:) of another method, and shape.Sizes has several values: such methods are not supported yet (#283)
# (said of the override that uses (super:) of another method, not of the method it overrides)
shape := class:
    Sizes()<transacts>:int = 1 | 2
    Other()<transacts>:int = 5
big := class(shape):
    Sizes<override>()<transacts>:int = (super:)Other() | 9
Main()<transacts>:void =
    for (X := big{}.Sizes()):
        Print("{X}")
