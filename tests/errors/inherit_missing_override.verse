# expect: Area is inherited from shape: mark it Area<override>
shape := class:
    Area():int = 0
square := class(shape):
    Area():int = 1
Main():void = Print("x")
