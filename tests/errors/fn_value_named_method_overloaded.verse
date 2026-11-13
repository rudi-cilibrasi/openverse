# expect: is an overloaded method of box: an overloaded method cannot be used as a value
# (Book of Verse ch. 6, "Capture", #503)
box := class:
    Get(X:int):int = X
    Get(X:int, ?Extra:int):int = X + Extra
Main():void =
    B := box{}
    F:type{_(:int, ?Extra:int):int} = B.Get
    Print("{F(1, ?Extra := 2)}")
