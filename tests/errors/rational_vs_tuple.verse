# expect: 3:20: '=' compares a rational with an int or a rational, not with tuple(int, int)
Main():void =
    if (R := 1 / 2, R = (1, 2)) then Print("x")
