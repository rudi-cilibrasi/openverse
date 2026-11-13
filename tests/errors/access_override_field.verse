# expect: <protected> on Size<override>: an override has the access of the member it overrides
shape := class:
    Size<protected>:int = 1
square := class(shape):
    Size<protected><override>:int = 2
Main():void = {}
