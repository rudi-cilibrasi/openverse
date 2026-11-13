# expect: '=' compares values of different types, []tuple(int, []int) and []tuple(int, []char32), with values in common
Main():void =
    X:[]tuple(int, []int) = array{(1, array{})}
    Y:[]tuple(int, []char32) = array{(1, array{})}
    if (X = Y) then Print("equal")
