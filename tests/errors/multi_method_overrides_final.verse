# expect: 6:4: shape.Sizes is <final>: it cannot be overridden
# (an overridden method with several values is still checked as a member: <final>)
shape := class:
    Sizes<final>()<transacts>:int = 1 | 2
big := class(shape):
    Sizes<override>()<transacts>:int = 1000
Main()<transacts>:void =
    for (X := big{}.Sizes()):
        Print("{X}")
