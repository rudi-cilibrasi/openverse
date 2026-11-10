# expect: 5:4: tri.Sides must have the signature of shape.Sides, which it overrides
shape := class<abstract>:
    Sides()<decides><transacts>:int
tri := class(shape):
    Sides<override>()<transacts>:int = 1 | 2
sq := class(shape):
    Sides<override>()<decides><transacts>:int = (4 | 5) > 4
Main()<transacts>:void =
    Ss : []shape = array{tri{}, sq{}}
    for (X : Ss, N := X.Sides[]) { Print("c {N}") }
