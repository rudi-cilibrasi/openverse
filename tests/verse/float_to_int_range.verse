# a float conversion out of the int range is the overflow error (#127 review: the API's integer-bounds error)
Main():void =
    Print("before")
    if (I := Floor[1.0e300]) then Print("{I}") else Print("fails")
    Print("after")
