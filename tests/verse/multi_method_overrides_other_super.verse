# A cross-method super call keeps the source class after inlining.
shape := class:
    Sizes()<transacts>:int = 1 | 2
    Other()<transacts>:int = 5
big := class(shape):
    Sizes<override>()<transacts>:int = (super:)Other() | 9
    Other<override>()<transacts>:int = 50
leaf := class(big):
    Other<override>()<transacts>:int = 99
Main()<transacts>:void =
    for (X := leaf{}.Sizes()):
        Print("{X}")
