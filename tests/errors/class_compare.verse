# expect: an operand of '=' must be comparable, and counter is a class
counter := class:
    N:int = 0

Main():void =
    A := counter{}
    if (A = counter{}) then Print("same")
