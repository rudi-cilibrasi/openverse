# expect: '=' compares values of different types, []tuple(int, []int) and []tuple(int, []char32), whose values in common Verse Core cannot compare
Main():void =
    X:[]tuple(int, []int) = array{(1, array{})}
    Y:[]tuple(int, []char32) = array{(1, array{})}
    if (X = Y) then Print("equal")
