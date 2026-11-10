# expect: 3:4: shape.Sides has several values, but an interface (shape) gives it a default implementation
shape := interface:
    Sides()<transacts>:int = 1 | 2
tri := class(shape):
    Sides<override>()<transacts>:int = 3
Main()<transacts>:void =
    S : shape = tri{}
    for (N := S.Sides()):
        Print("{N}")
