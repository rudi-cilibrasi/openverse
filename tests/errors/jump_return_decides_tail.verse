# expect: 4:21: a return in a <decides> function must be in tail position
# In a <decides> function, whose body is a failure context, a return only in tail position (Return.versetest:159)
F(X:int)<decides>:int =
    if (X <> 0) then return X
    X > 0
    X
Main():void = if (V := F[1]) then Print("{V}")
