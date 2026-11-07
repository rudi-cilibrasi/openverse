# expect: shape.Area is <final>: it cannot be overridden
shape := class:
    Area<final>():int = 0
square := class(shape):
    Area<override>():int = 1
Main():void = Print("x")
