# expect: expected ',' or ')', found ':'
Main():void =
    Inner(X:int):int = X
    Print(Inner(7))
