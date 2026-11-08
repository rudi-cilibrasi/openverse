# expect: expected type{_(:int)<computes>:int}, found type{_(:int):int}
# a function with heap effects is no <computes> function
Pure(F:type{_(:int)<computes>:int}):int = F(1)
W(X:int):int =
    var Y:int = X
    set Y += 1
    Y
Main():void = Print("{Pure(W)}")
