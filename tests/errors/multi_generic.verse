# expect: 2:0: Both has several values and is generic
Both(X:t, Y:t where t:type):t = X | Y
Main():void =
    for (V := Both(1, 2)) { Print("{V}") }
