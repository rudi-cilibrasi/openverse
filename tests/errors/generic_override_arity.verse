# expect: Tag has 2 type parameter(s) of its own, and shape.Tag, which it overrides, 1
shape := class<abstract>:
    Tag(X:u where u:type):tuple(string, u)
square := class(shape):
    Tag<override>(X:u, Y:v where u:type, v:type):tuple(string, u) = ("bad", X)
Main():void = Print("x")
