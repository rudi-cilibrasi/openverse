# expect: square.Area must have the signature of shape.Area
shape := class:
    Area():int = 0
square := class(shape):
    Area<override>():string = "one"
Main():void = Print("x")
