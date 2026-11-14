# A definition `X := e` names a type when `e` is one (a type alias); a
# constant states its type, `X:t = e` (Book of Verse ch. 16: "type inference
# with := alone is not allowed"): a cast, a conversion to any, a function's
# value or another constant's
shape := class<computes>:
    Sides:int = 3
square := class<computes>(shape):
    Side:int = 2
figure := shape                   # a type: shape
S:square = square{}
AsShape:shape = shape(S)          # a constant: S cast to shape
Anything:any = any(S)             # a constant: an any
Count:int = 7                     # a constant
Again:int = Count                 # a constant, from a constant
Twice(X:int):int = X + X
Doubler:int->int = Twice          # a constant: a function's value
pair(t:type) := tuple(t, t)
ints := pair(int)                 # a type: tuple(int, int)

Main():void =
    F:figure = AsShape
    P:ints = (Again, Doubler(Count))
    Print("{F.Sides} {P(0)} {P(1)}")
