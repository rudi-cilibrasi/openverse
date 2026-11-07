# expect: '=' compares values of different types, char32 and int
Main():void =
    if (0u41 = 65) {}
