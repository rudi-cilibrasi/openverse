# expect: defer: is a statement: it has no value
V(X:void):void = Print("v")
Main():void =
    V(defer{Print("a")})
