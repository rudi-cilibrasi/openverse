# expect: square.Area allows the effect <allocates>, which shape.Area, which it overrides, does not
shape := class<abstract>:
    var Hits:int = 0
    Area()<reads>:int
square := class(shape):
    S:int
    Area<override>()<transacts>:int =
        set Hits += 1
        S * S
Main():void = Print("{square{S := 2}.Area()}")
