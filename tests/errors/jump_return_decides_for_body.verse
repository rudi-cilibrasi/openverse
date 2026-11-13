# expect: 4:35: a return in a <decides> function must be in tail position
# A <decides> function's return in a for's body is not in tail position (Return.versetest:163)
F(X:int)<decides>:int =
    for (Y := 0..X, X * Y = 100) { return Y }
    X > 0
    X
Main():void = if (V := F[1]) then Print("{V}")
