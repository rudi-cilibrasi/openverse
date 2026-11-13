# expect: expected type{_(?X:int):int}, found type{_(:int):int}
# A named parameter is not a positional one (#503)
F(X:int):int = X
Main():void =
    G:type{_(?X:int):int} = F
    Print("{G(?X := 1)}")
