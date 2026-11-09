# expect: 6:4: big.Sizes allows the effect <allocates>, which shape.Sizes, which it overrides, does not
# (its effects against the one it overrides)
shape := class:
    Sizes()<computes>:int = 1 | 2
big := class(shape):
    Sizes<override>()<transacts>:int =
        Print("side")
        1000
Main()<transacts>:void =
    for (X := big{}.Sizes()):
        Print("{X}")
