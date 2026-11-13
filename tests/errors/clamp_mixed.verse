# expect: 4:20: Clamp takes floats or ints, found float and int
# Clamp's three arguments are all ints or all floats.
Main():void =
    X := Clamp(1.0, 2, 3.0)
