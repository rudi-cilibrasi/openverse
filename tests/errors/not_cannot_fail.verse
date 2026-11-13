# expect: the operand of not cannot fail
# (as an if's condition and logic{…}: a failure context of an expression that
# cannot fail; not of it always fails)
Main():void =
    X:int = 1
    if (not X) then Print("never")
