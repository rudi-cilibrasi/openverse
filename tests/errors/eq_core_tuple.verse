# expect: '=' compares values of different types, tuple(char32, int) and tuple(int, int)
Main():void =
    X:tuple(char32, int) = (0u41, 1)
    Y:tuple(int, int) = (65, 1)
    if (X = Y) {}
