# expect: 3:20: '=' compares values of different types, []int and []rational (an int and a rational inside them: convert the ints first)
Main():void =
    if (R := 2 / 2, array{1} = array{R}) then Print("x")
