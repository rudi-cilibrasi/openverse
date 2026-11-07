# expect: F is overloaded: an overloaded function cannot be used as a value
F(X:int):int = 1
F(S:string):int = 0
Main():void =
    G := F
    Print("x")
