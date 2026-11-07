# expect: square must implement Area (declared abstract in shape)
shape := class<abstract>:
    Area():int
square := class(shape):
    Side:int
Main():void = Print("x")
