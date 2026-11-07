# expect: '=' compares values of different types, ?char32 and ?int
Main():void =
    X:?char32 = option{0u41}
    Y:?int = option{65}
    if (X = Y) {}
