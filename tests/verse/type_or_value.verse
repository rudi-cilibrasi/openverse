# A definition `X := e` names a type when `e` is one (a type alias), and is
# a constant otherwise: a cast, a conversion to any, a function's value or
# another constant's
shape := class:
    Sides:int = 3
square := class(shape):
    Side:int = 2
figure := shape                   # a type: shape
S:square = square{}
AsShape := shape(S)               # a constant: S cast to shape
Anything := any(S)                # a constant: an any
Count := 7                        # a constant
Again := Count                    # a constant, from a constant
Twice(X:int):int = X + X
Doubler := Twice                  # a constant: a function's value
pair(t:type) := tuple(t, t)
ints := pair(int)                 # a type: tuple(int, int)

Main():void =
    F:figure = AsShape
    P:ints = (Again, Doubler(Count))
    Print("{F.Sides} {P(0)} {P(1)}")
