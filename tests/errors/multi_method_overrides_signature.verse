# expect: 6:4: big.Sizes must have the signature of shape.Sizes, which it overrides
# (its signature against the one it overrides)
shape := class:
    Sizes()<transacts>:int = 1 | 2
big := class(shape):
    Sizes<override>()<decides><transacts>:int = 1000
Main()<transacts>:void =
    for (X := shape{}.Sizes()):
        Print("{X}")
