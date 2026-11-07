# expect: square.Tag must have the signature of shape.Tag
shape := class<abstract>:
    Tag(X:u where u:type):tuple(string, u)
square := class(shape):
    Tag<override>(X:w where w:type):tuple(string, int) = ("bad", 0)
Main():void = Print("x")
