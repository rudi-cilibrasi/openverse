# expect: expected concrete_subtype(shape), found shape
shape := class<abstract>:
    Sides():int
F():void =
    X:concrete_subtype(shape) = shape
Main():void = {}
